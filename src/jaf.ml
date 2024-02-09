(* Copyright (C) 2021 Nunuhara Cabbage <nunuhara@haniwa.technology>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

open Core
open Printf

type unary_op =
  | UPlus
  | UMinus
  | LogNot
  | BitNot
  | AddrOf
  | PreInc
  | PreDec
  | PostInc
  | PostDec

type binary_op =
  | Plus
  | Minus
  | Times
  | Divide
  | Modulo
  | Equal
  | NEqual
  | RefEqual
  | RefNEqual
  | LT
  | GT
  | LTE
  | GTE
  | LogOr
  | LogAnd
  | BitOr
  | BitXor
  | BitAnd
  | LShift
  | RShift

type assign_op =
  | EqAssign
  | PlusAssign
  | MinusAssign
  | TimesAssign
  | DivideAssign
  | ModuloAssign
  | OrAssign
  | XorAssign
  | AndAssign
  | LShiftAssign
  | RShiftAssign

type type_specifier = { mutable data : data_type; is_ref : bool }

and data_type =
  | Untyped
  | Unresolved of string
  | Void
  | Int
  | Bool
  | Float
  | String
  | Struct of string * int
  (*| Enum*)
  | Array of type_specifier
  | Wrap of type_specifier
  | HLLParam
  | HLLFunc
  | Delegate of string * int
  | FuncType of string * int
  | IMainSystem

type ident_type =
  | LocalVariable of int
  | GlobalVariable of int
  | GlobalConstant
  | FunctionName of int
  | HLLName of int
  | System
  | BuiltinFunction of Bytecode.builtin

type member_type =
  | ClassVariable of int * int
  | ClassMethod of int * int
  | HLLFunction of int * int
  | SystemFunction of Bytecode.syscall
  | BuiltinMethod of Bytecode.builtin

type call_type =
  | FunctionCall of int
  | MethodCall of int * int
  | HLLCall of int * int * int
  | SystemCall of Bytecode.syscall
  | BuiltinCall of Bytecode.builtin
  | FuncTypeCall of int
  | DelegateCall of int

type expression = {
  mutable valuetype : Ain.Type.t option;
  mutable node : ast_expression;
  loc : Lexing.position * Lexing.position;
}

and ast_expression =
  | ConstInt of int
  | ConstFloat of float
  | ConstChar of string
  | ConstString of string
  | Ident of string * ident_type option
  | Unary of unary_op * expression
  | Binary of binary_op * expression * expression
  | Assign of assign_op * expression * expression
  | Seq of expression * expression
  | Ternary of expression * expression * expression
  | Cast of data_type * expression
  | Subscript of expression * expression
  | Member of expression * string * member_type option
  | Call of expression * expression list * call_type option
  | New of data_type * expression list * int option
  | This
  | Null

type statement = {
  mutable node : ast_statement;
  mutable delete_vars : int list;
  loc : Lexing.position * Lexing.position;
}

and ast_statement =
  | EmptyStatement
  | Declarations of variable list
  | Expression of expression
  | Compound of statement list
  | Labeled of string * statement
  | If of expression * statement * statement
  | While of expression * statement
  | DoWhile of expression * statement
  | For of statement * expression option * expression option * statement
  | Goto of string
  | Continue
  | Break
  | Switch of expression * statement list
  | Case of expression * statement
  | Default of statement
  | Return of expression option
  | MessageCall of string * string option * int option
  | RefAssign of expression * expression
  | ObjSwap of expression * expression

and variable = {
  name : string;
  location : Lexing.position * Lexing.position;
  array_dim : expression list;
  is_const : bool;
  type_spec : type_specifier;
  initval : expression option;
  mutable index : int option;
}

type fundecl = {
  mutable name : string;
  loc : Lexing.position * Lexing.position;
  struct_name : string option;
  return : type_specifier;
  params : variable list;
  body : statement list;
  is_label : bool;
  mutable index : int option;
  mutable class_index : int option;
}

let mangled_name fdecl =
  match fdecl.struct_name with
  | Some s -> s ^ "@" ^ fdecl.name
  | None -> fdecl.name

type access_specifier = Public | Private

type struct_declaration =
  | AccessSpecifier of access_specifier
  | MemberDecl of variable
  | Constructor of fundecl
  | Destructor of fundecl
  | Method of fundecl

type structdecl = {
  name : string;
  is_class : bool;
  loc : Lexing.position * Lexing.position;
  decls : struct_declaration list;
}

type enumdecl = {
  name : string option;
  loc : Lexing.position * Lexing.position;
  values : (string * expression option) list;
}

type declaration =
  | Function of fundecl
  | Global of variable
  | FuncTypeDef of fundecl
  | DelegateDef of fundecl
  | StructDef of structdecl
  | Enum of enumdecl

type ast_node =
  | ASTExpression of expression
  | ASTStatement of statement
  | ASTVariable of variable
  | ASTDeclaration of declaration

let ast_node_pos = function
  | ASTExpression e -> e.loc
  | ASTStatement s -> s.loc
  | ASTVariable v -> v.location
  | ASTDeclaration d -> (
      match d with
      | Function f -> f.loc
      | Global v -> v.location
      | FuncTypeDef f -> f.loc
      | DelegateDef f -> f.loc
      | StructDef s -> s.loc
      | Enum e -> e.loc)

type context = { ain : Ain.t; mutable const_vars : variable list }

type resolved_name =
  | ResolvedLocal of variable
  | ResolvedConstant of variable
  | ResolvedGlobal of Ain.Variable.t
  | ResolvedFunction of int
  | ResolvedLibrary of int
  | ResolvedSystem
  | ResolvedBuiltin of Bytecode.builtin
  | UnresolvedName

class ivisitor ctx =
  object (self)
    val environment =
      object (self)
        val mutable stack = []
        val mutable variables = []
        val mutable current_function = None
        method push = stack <- variables :: stack

        method pop =
          match stack with
          | [] -> failwith "visitor tried to pop root environment"
          | prev :: rest ->
              variables <- prev;
              stack <- rest

        method push_var decl = variables <- decl :: variables

        method var_list =
          List.append variables (List.fold stack ~init:[] ~f:List.append)

        method var_id_list =
          List.map self#var_list ~f:(fun (v : variable) ->
              Option.value_exn v.index)

        method enter_function decl =
          self#push;
          current_function <- Some decl;
          List.iter decl.params ~f:self#push_var

        method leave_function =
          self#pop;
          current_function <- None

        method current_function = current_function

        method current_class =
          match current_function with Some f -> f.class_index | None -> None

        method get_local name =
          let var_eq _ (v : variable) = String.equal v.name name in
          let rec search vars rest =
            match List.findi vars ~f:var_eq with
            | Some (_, v) -> Some v
            | None -> (
                match rest with [] -> None | prev :: rest -> search prev rest)
          in
          search variables stack

        method resolve name =
          let ain_resolve ain =
            match Ain.get_global ain name with
            | Some g -> ResolvedGlobal g
            | None -> (
                match Ain.get_function ain name with
                | Some f -> ResolvedFunction f.index
                | None -> (
                    match Ain.get_library_index ain name with
                    | Some i -> ResolvedLibrary i
                    | None -> UnresolvedName))
          in
          match name with
          | "system" ->
              (* NOTE: on ain v11+, "system" is a library *)
              if Ain.version_gte ctx.ain (11, 0) then
                match Ain.get_library_index ctx.ain "system" with
                | Some i -> ResolvedLibrary i
                | None -> UnresolvedName
              else ResolvedSystem
          | "assert" ->
              ResolvedBuiltin
                (Option.value_exn
                   (Bytecode.builtin_function_of_string "assert"))
          | _ -> (
              match self#get_local name with
              | Some v -> ResolvedLocal v
              | None -> (
                  match
                    List.findi ctx.const_vars ~f:(fun _ (v : variable) ->
                        String.equal v.name name)
                  with
                  | Some (_, v) -> ResolvedConstant v
                  | None -> ain_resolve ctx.ain))
      end

    method visit_expression (e : expression) =
      match e.node with
      | ConstInt _ -> ()
      | ConstFloat _ -> ()
      | ConstChar _ -> ()
      | ConstString _ -> ()
      | Ident (_, _) -> ()
      | Unary (_, e) -> self#visit_expression e
      | Binary (_, lhs, rhs) ->
          self#visit_expression lhs;
          self#visit_expression rhs
      | Assign (_, lhs, rhs) ->
          self#visit_expression lhs;
          self#visit_expression rhs
      | Seq (a, b) ->
          self#visit_expression a;
          self#visit_expression b
      | Ternary (a, b, c) ->
          self#visit_expression a;
          self#visit_expression b;
          self#visit_expression c
      | Cast (_, obj) -> self#visit_expression obj
      | Subscript (arr, i) ->
          self#visit_expression arr;
          self#visit_expression i
      | Member (obj, _, _) -> self#visit_expression obj
      | Call (f, args, _) ->
          self#visit_expression f;
          List.iter args ~f:self#visit_expression
      | New (_, args, _) -> List.iter args ~f:self#visit_expression
      | This -> ()
      | Null -> ()

    method visit_statement (s : statement) =
      match s.node with
      | EmptyStatement -> ()
      | Declarations ds -> List.iter ds ~f:self#visit_local_variable
      | Expression e -> self#visit_expression e
      | Compound stmts ->
          environment#push;
          List.iter stmts ~f:self#visit_statement;
          environment#pop
      | Labeled (_, a) -> self#visit_statement a
      | If (test, cons, alt) ->
          self#visit_expression test;
          self#visit_statement cons;
          self#visit_statement alt
      | While (test, body) ->
          self#visit_expression test;
          self#visit_statement body
      | DoWhile (test, body) ->
          self#visit_statement body;
          self#visit_expression test
      | For (init, test, inc, body) ->
          environment#push;
          self#visit_statement init;
          Option.iter test ~f:self#visit_expression;
          Option.iter inc ~f:self#visit_expression;
          self#visit_statement body;
          environment#pop
      | Goto _ -> ()
      | Continue -> ()
      | Break -> ()
      | Switch (e, stmts) ->
          self#visit_expression e;
          List.iter stmts ~f:self#visit_statement
      | Case (e, stmt) ->
          self#visit_expression e;
          self#visit_statement stmt
      | Default stmt -> self#visit_statement stmt
      | Return e -> Option.iter e ~f:self#visit_expression
      | MessageCall (_, _, _) -> ()
      | RefAssign (a, b) ->
          self#visit_expression a;
          self#visit_expression b
      | ObjSwap (a, b) ->
          self#visit_expression a;
          self#visit_expression b

    method visit_local_variable v =
      List.iter v.array_dim ~f:self#visit_expression;
      Option.iter v.initval ~f:self#visit_expression;
      environment#push_var v

    method visit_fundecl f =
      environment#enter_function f;
      List.iter f.body ~f:self#visit_statement;
      environment#leave_function

    method visit_declaration d =
      let visit_vardecl d =
        List.iter d.array_dim ~f:self#visit_expression;
        Option.iter d.initval ~f:self#visit_expression
      in
      match d with
      | Global g -> visit_vardecl g
      | Function f -> self#visit_fundecl f
      | FuncTypeDef _ -> ()
      | DelegateDef _ -> ()
      | StructDef s ->
          let visit_structdecl = function
            | AccessSpecifier _ -> ()
            | MemberDecl d -> visit_vardecl d
            | Constructor f -> self#visit_fundecl f
            | Destructor f -> self#visit_fundecl f
            | Method f -> self#visit_fundecl f
          in
          List.iter s.decls ~f:visit_structdecl
      | Enum enum ->
          let visit_enumval (_, expr) =
            Option.iter expr ~f:self#visit_expression
          in
          List.iter enum.values ~f:visit_enumval

    method visit_toplevel decls = List.iter decls ~f:self#visit_declaration
  end

let unary_op_to_string op =
  match op with
  | UPlus -> "+"
  | UMinus -> "-"
  | LogNot -> "!"
  | BitNot -> "~"
  | AddrOf -> "&"
  | PreInc -> "++"
  | PreDec -> "--"
  | PostInc -> "++"
  | PostDec -> "--"

let binary_op_to_string op =
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | Modulo -> "%"
  | Equal -> "=="
  | NEqual -> "!="
  | RefEqual -> "==="
  | RefNEqual -> "!=="
  | LT -> "<"
  | GT -> ">"
  | LTE -> "<="
  | GTE -> ">="
  | LogOr -> "||"
  | LogAnd -> "&&"
  | BitOr -> "|"
  | BitXor -> "^"
  | BitAnd -> "&"
  | LShift -> "<<"
  | RShift -> ">>"

let assign_op_to_string op =
  match op with
  | EqAssign -> "="
  | PlusAssign -> "+="
  | MinusAssign -> "-="
  | TimesAssign -> "*="
  | DivideAssign -> "/="
  | ModuloAssign -> "%="
  | OrAssign -> "|="
  | XorAssign -> "^="
  | AndAssign -> "&="
  | LShiftAssign -> "<<="
  | RShiftAssign -> ">>="

let rec data_type_to_string = function
  | Untyped -> "untyped"
  | Unresolved s -> "Unresolved<" ^ s ^ ">"
  | Void -> "void"
  | Int -> "int"
  | Bool -> "bool"
  | Float -> "float"
  | String -> "string"
  | Struct (s, _) | FuncType (s, _) | Delegate (s, _) -> s
  | Array t -> "array<" ^ type_spec_to_string t ^ ">" (* TODO: rank *)
  | Wrap t -> "wrap<" ^ type_spec_to_string t ^ ">"
  | HLLParam -> "hll_param"
  | HLLFunc -> "hll_func"
  | IMainSystem -> "IMainSystem"

and type_spec_to_string ts =
  if ts.is_ref then "ref " ^ data_type_to_string ts.data
  else data_type_to_string ts.data

let rec expr_to_string (e : expression) =
  let arglist_to_string = function
    | [] -> "()"
    | arg :: args ->
        let rec loop result = function
          | [] -> result
          | arg :: args ->
              loop (sprintf "%s, %s" result (expr_to_string arg)) args
        in
        sprintf "(%s)" (loop (expr_to_string arg) args)
  in
  match e.node with
  | ConstInt i -> string_of_int i
  | ConstFloat f -> string_of_float f
  | ConstChar s -> sprintf "'%s'" s
  | ConstString s -> sprintf "\"%s\"" s
  | Ident (s, _) -> s
  | Unary (op, e) -> (
      match op with
      | PostInc | PostDec -> expr_to_string e ^ unary_op_to_string op
      | _ -> unary_op_to_string op ^ expr_to_string e)
  | Binary (op, a, b) ->
      sprintf "%s %s %s" (expr_to_string a) (binary_op_to_string op)
        (expr_to_string b)
  | Assign (op, a, b) ->
      sprintf "%s %s %s" (expr_to_string a) (assign_op_to_string op)
        (expr_to_string b)
  | Seq (a, b) -> sprintf "%s, %s" (expr_to_string a) (expr_to_string b)
  | Ternary (a, b, c) ->
      sprintf "%s ? %s : %s" (expr_to_string a) (expr_to_string b)
        (expr_to_string c)
  | Cast (t, e) -> sprintf "(%s)%s" (data_type_to_string t) (expr_to_string e)
  | Subscript (e, i) -> sprintf "%s[%s]" (expr_to_string e) (expr_to_string i)
  | Member (e, s, _) -> sprintf "%s.%s" (expr_to_string e) s
  | Call (f, args, _) ->
      sprintf "%s%s" (expr_to_string f) (arglist_to_string args)
  | New (t, args, _) ->
      sprintf "new %s%s" (data_type_to_string t) (arglist_to_string args)
  | This -> "this"
  | Null -> "NULL"

let rec stmt_to_string (stmt : statement) =
  match stmt.node with
  | EmptyStatement -> ";"
  | Declarations ds ->
      List.fold (List.map ds ~f:var_to_string) ~init:"" ~f:( ^ )
  | Expression e -> expr_to_string e ^ ";"
  | Compound stmts ->
      stmts |> List.map ~f:stmt_to_string |> List.fold ~init:"" ~f:( ^ )
  | Labeled (label, stmt) -> sprintf "%s: %s" label (stmt_to_string stmt)
  | If (test, body, alt) ->
      let s_test = expr_to_string test in
      let s_body = stmt_to_string body in
      let s_alt = stmt_to_string alt in
      sprintf "if (%s) %s else %s" s_test s_body s_alt
  | While (test, body) ->
      sprintf "while (%s) %s" (expr_to_string test) (stmt_to_string body)
  | DoWhile (test, body) ->
      sprintf "do %s while (%s);" (stmt_to_string body) (expr_to_string test)
  | For (init, test, inc, body) ->
      let expr_opt_to_string = Option.value_map ~default:"" ~f:expr_to_string in
      let s_init = stmt_to_string init in
      let s_test = expr_opt_to_string test in
      let s_body = stmt_to_string body in
      let s_inc = expr_opt_to_string inc in
      sprintf "for (%s %s %s) %s" s_init s_test s_inc s_body
  | Goto label -> sprintf "goto %s;" label
  | Continue -> "continue;"
  | Break -> "break;"
  | Switch (expr, body) ->
      let s_expr = expr_to_string expr in
      let s_body =
        body |> List.map ~f:stmt_to_string |> List.fold ~init:"" ~f:( ^ )
      in
      sprintf "switch (%s) { %s }" s_expr s_body
  | Case (expr, stmt) ->
      sprintf "case %s: %s" (expr_to_string expr) (stmt_to_string stmt)
  | Default stmt -> sprintf "default: %s" (stmt_to_string stmt)
  | Return None -> "return;"
  | Return (Some e) -> sprintf "return %s;" (expr_to_string e)
  | MessageCall (msg, f, _) -> (
      match f with
      | Some name -> sprintf "'%s' %s;" msg name
      | None -> sprintf "'%s';" msg)
  | RefAssign (dst, src) ->
      sprintf "%s <- %s;" (expr_to_string dst) (expr_to_string src)
  | ObjSwap (a, b) -> sprintf "%s <=> %s;" (expr_to_string a) (expr_to_string b)

and var_to_string' d =
  let t = type_spec_to_string d.type_spec in
  let dim_iter l r = l ^ sprintf "[%s]" (expr_to_string r) in
  let dims = List.fold d.array_dim ~init:"" ~f:dim_iter in
  let init =
    match d.initval with
    | None -> ""
    | Some e -> sprintf " = %s" (expr_to_string e)
  in
  sprintf "%s %s%s%s" t dims d.name init

and var_to_string d = var_to_string' d ^ ";"

let decl_to_string d =
  let params_to_string = function
    | [] -> "()"
    | p :: ps ->
        let rec loop result = function
          | [] -> result
          | p :: ps -> loop (sprintf "%s, %s" result (var_to_string' p)) ps
        in
        sprintf "(%s)" (loop (var_to_string' p) ps)
  in
  let block_to_string block =
    List.fold (List.map block ~f:stmt_to_string) ~init:"" ~f:( ^ )
  in
  match d with
  | Global d -> var_to_string d
  | Function d ->
      let return = type_spec_to_string d.return in
      let params = params_to_string d.params in
      let body = block_to_string d.body in
      sprintf "%s %s%s { %s }" return d.name params body
  | FuncTypeDef d ->
      let return = type_spec_to_string d.return in
      let params = params_to_string d.params in
      sprintf "functype %s %s%s;" return d.name params
  | DelegateDef d ->
      let return = type_spec_to_string d.return in
      let params = params_to_string d.params in
      sprintf "delegate %s %s%s;" return d.name params
  | StructDef d ->
      let sdecl_to_string = function
        | AccessSpecifier Public -> "public:"
        | AccessSpecifier Private -> "private:"
        | MemberDecl d -> var_to_string d
        | Constructor d ->
            let params = params_to_string d.params in
            let body = block_to_string d.body in
            sprintf "%s%s { %s }" d.name params body
        | Destructor d ->
            let params = params_to_string d.params in
            let body = block_to_string d.body in
            sprintf "~%s%s { %s }" d.name params body
        | Method d ->
            let return = type_spec_to_string d.return in
            let params = params_to_string d.params in
            let body = block_to_string d.body in
            sprintf "%s %s%s { %s }" return d.name params body
      in
      let body =
        List.fold (List.map d.decls ~f:sdecl_to_string) ~init:"" ~f:( ^ )
      in
      sprintf "%s %s { %s };"
        (if d.is_class then "class" else "struct")
        d.name body
  | Enum d ->
      let enumval_to_string = function
        | s, None -> s
        | s, Some e -> sprintf "%s = %s" s (expr_to_string e)
      in
      let enumvals_fold l r = l ^ ", " ^ r in
      let body =
        List.fold
          (List.map d.values ~f:enumval_to_string)
          ~init:"" ~f:enumvals_fold
      in
      let name = match d.name with None -> "" | Some s -> s ^ " " in
      sprintf "enum %s{ %s };" name body

let ast_to_string = function
  | ASTExpression e -> expr_to_string e
  | ASTStatement s -> stmt_to_string s
  | ASTVariable v -> var_to_string v
  | ASTDeclaration d -> decl_to_string d

let rec jaf_to_ain_data_type data =
  match data with
  | Untyped -> failwith "tried to convert Untyped to ain data type"
  | Unresolved _ -> failwith "tried to convert Unresolved to ain data type"
  | Void -> Ain.Type.Void
  | Int -> Ain.Type.Int
  | Bool -> Ain.Type.Bool
  | Float -> Ain.Type.Float
  | String -> Ain.Type.String
  | Struct (_, i) -> Ain.Type.Struct i
  | Array t -> Ain.Type.Array (jaf_to_ain_type t)
  | Wrap t -> Ain.Type.Wrap (jaf_to_ain_type t)
  | HLLParam -> Ain.Type.HLLParam
  | HLLFunc -> Ain.Type.HLLFunc
  | Delegate (_, i) -> Ain.Type.Delegate i
  | FuncType (_, i) -> Ain.Type.FuncType i
  | IMainSystem -> Ain.Type.IMainSystem

and jaf_to_ain_type spec =
  Ain.Type.make ~is_ref:spec.is_ref (jaf_to_ain_data_type spec.data)

let jaf_to_ain_variables j_p =
  let rec convert_params (params : variable list) (result : Ain.Variable.t list)
      index =
    match params with
    | [] -> List.rev result
    | x :: xs -> (
        let var =
          Ain.Variable.make ~index x.name (jaf_to_ain_type x.type_spec)
        in
        match x.type_spec with
        | { data = Int | Bool | Float | FuncType (_, _); is_ref = true } ->
            let void =
              Ain.Variable.make ~index:(index + 1) "<void>" (Ain.Type.make Void)
            in
            convert_params xs (void :: var :: result) (index + 2)
        | _ -> convert_params xs (var :: result) (index + 1))
  in
  convert_params j_p [] 0

let jaf_to_ain_function j_f (a_f : Ain.Function.t) =
  let vars = jaf_to_ain_variables j_f.params in
  {
    a_f with
    vars;
    nr_args = List.length vars;
    return_type = jaf_to_ain_type j_f.return;
    is_label = j_f.is_label;
  }

let jaf_to_ain_struct j_s (a_s : Ain.Struct.t) =
  let members =
    List.filter_map j_s.decls ~f:(function MemberDecl v -> Some v | _ -> None)
    |> jaf_to_ain_variables
  in
  let is_ctor = function Constructor _ -> true | _ -> false in
  let constructor =
    match List.find j_s.decls ~f:is_ctor with
    | Some (Constructor ctor) -> Option.value_exn ctor.index
    | _ -> -1
  in
  let is_dtor = function Destructor _ -> true | _ -> false in
  let destructor =
    match List.find j_s.decls ~f:is_dtor with
    | Some (Destructor dtor) -> Option.value_exn dtor.index
    | _ -> -1
  in
  {
    a_s with
    members;
    constructor;
    destructor
    (* TODO: interfaces *)
    (* TODO: vmethods *);
  }

let jaf_to_ain_functype j_f (a_f : Ain.FunctionType.t) =
  let variables = jaf_to_ain_variables j_f.params in
  {
    a_f with
    variables;
    nr_arguments = List.length variables;
    return_type = jaf_to_ain_type j_f.return;
  }

let jaf_to_ain_hll_function j_f =
  let jaf_to_ain_hll_argument (param : variable) =
    Ain.Library.Argument.create param.name (jaf_to_ain_type param.type_spec)
  in
  let return_type = jaf_to_ain_type j_f.return in
  let arguments = List.map j_f.params ~f:jaf_to_ain_hll_argument in
  Ain.Library.Function.create j_f.name return_type arguments
