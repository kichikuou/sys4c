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

open Base
open Printf

type location = Lexing.position * Lexing.position

let dummy_location = (Lexing.dummy_pos, Lexing.dummy_pos)

type unary_op =
  | UPlus
  | UMinus
  | LogNot
  | BitNot
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
  | CharAssign

type jaf_type =
  | Untyped
  | Unresolved of string
  | Void
  | Int
  | LongInt
  | Bool
  | Float
  | String
  | Struct of string * int
  (*| Enum*)
  | Ref of jaf_type
  | Array of jaf_type
  | Wrap of jaf_type
  | HLLParam
  | HLLFunc
  | Delegate of (string * int * jaf_type) option
  | FuncType of (string * int) option
  | IMainSystem
  | NullType
  | TyFunction of function_type
  | TyMethod of function_type
  | MemberPtr of string * jaf_type

and function_type = jaf_type list * jaf_type

let jaf_type_equal (a : jaf_type) b = Poly.equal a b

let ft_compatible (args, ret) (args', ret') =
  jaf_type_equal ret ret'
  && List.length args = List.length args'
  && List.for_all2_exn args args' ~f:jaf_type_equal

let is_scalar = function
  | Int | Bool | Float | LongInt | FuncType _ -> true
  | _ -> false

let is_ref_scalar = function
  | Ref (Int | Bool | Float | LongInt | FuncType _) -> true
  | _ -> false

let rec array_rank = function Array t -> 1 + array_rank t | _ -> 0

type type_specifier = { mutable ty : jaf_type; location : location }

type ident_type =
  | UnresolvedIdent
  | LocalVariable of int
  | GlobalVariable of int
  | GlobalConstant
  | FunctionName of string
  | HLLName
  | System
  | BuiltinFunction of Bytecode.builtin

type member_type =
  | UnresolvedMember
  | ClassVariable of int
  | ClassConst of string
  | ClassMethod of string * int
  | HLLFunction of string * string
  | SystemFunction of Bytecode.syscall
  | BuiltinMethod of Bytecode.builtin

type variable_type = Parameter | LocalVar | GlobalVar | ClassVar

type call_type =
  | UnresolvedCall
  | FunctionCall of int
  | MethodCall of int * int
  | HLLCall of int * int
  | SystemCall of Bytecode.syscall
  | BuiltinCall of Bytecode.builtin
  | FuncTypeCall of int
  | DelegateCall of int

type expression = {
  mutable ty : jaf_type;
  mutable node : ast_expression;
  loc : location;
}

and ast_expression =
  | ConstInt of int
  | ConstFloat of float
  | ConstChar of string
  | ConstString of string
  | Ident of string * ident_type
  | FuncAddr of string * int option
  | MemberAddr of string * string * member_type
  | Unary of unary_op * expression
  | Binary of binary_op * expression * expression
  | Assign of assign_op * expression * expression
  | Seq of expression * expression
  | Ternary of expression * expression * expression
  | Cast of jaf_type * expression
  | Subscript of expression * expression
  | Member of expression * string * member_type
  | Call of expression * expression option list * call_type
  | New of type_specifier
  | DummyRef of int * expression
  | This
  | Null

let make_expr ?(ty = Untyped) ?(loc = dummy_location) node = { ty; node; loc }
let clone_expr (e : expression) = { e with loc = e.loc }

type statement = {
  mutable node : ast_statement;
  mutable delete_vars : int list;
  loc : location;
}

and ast_statement =
  | EmptyStatement
  | Declarations of vardecls
  | Expression of expression
  | Compound of statement list
  | Label of string
  | If of expression * statement * statement
  | While of expression * statement
  | DoWhile of expression * statement
  | For of statement * expression option * expression option * statement
  | Goto of string
  | Continue
  | Break
  | Switch of expression * statement list
  | Case of expression
  | Default
  | Return of expression option
  | Jump of string
  | Jumps of expression
  | Message of string
  | RefAssign of expression * expression
  | ObjSwap of expression * expression

and variable = {
  name : string;
  location : location;
  array_dim : expression list;
  is_const : bool;
  mutable is_private : bool;
  kind : variable_type;
  type_spec : type_specifier;
  initval : expression option;
  mutable index : int option;
}

and vardecls = {
  decl_loc : location;
  is_const_decls : bool;
  typespec : type_specifier;
  vars : variable list;
}

type fundecl = {
  mutable name : string;
  loc : location;
  return : type_specifier;
  mutable params : variable list;
  mutable body : statement list option;
  is_label : bool;
  mutable is_private : bool;
  mutable index : int option;
  mutable class_name : string option;
  mutable class_index : int option;
}

let ft_of_fundecl fundecl =
  let args = List.map fundecl.params ~f:(fun p -> p.type_spec.ty) in
  let ret = fundecl.return.ty in
  (args, ret)

let is_constructor (f : fundecl) =
  match f.class_name with Some s -> String.equal f.name s | _ -> false

let mangled_name fdecl =
  match fdecl.class_name with
  | Some s ->
      s
      ^
      if String.equal fdecl.name s then "@0"
      else if String.equal fdecl.name ("~" ^ s) then "@1"
      else "@" ^ fdecl.name
  | None -> fdecl.name

type access_specifier = Public | Private

type struct_declaration =
  | AccessSpecifier of access_specifier
  | MemberDecl of vardecls
  | Constructor of fundecl
  | Destructor of fundecl
  | Method of fundecl

type structdecl = {
  name : string;
  is_class : bool;
  loc : location;
  decls : struct_declaration list;
}

type enumdecl = {
  name : string option;
  loc : location;
  values : (string * expression option) list;
}

type global_group = { name : string; loc : location; vardecls : vardecls list }

type declaration =
  | Function of fundecl
  | Global of vardecls
  | GlobalGroup of global_group
  | FuncTypeDef of fundecl
  | DelegateDef of fundecl
  | StructDef of structdecl
  | Enum of enumdecl

type ast_node =
  | ASTExpression of expression
  | ASTStatement of statement
  | ASTVariable of variable
  | ASTDeclaration of declaration
  | ASTStructDecl of struct_declaration
  | ASTType of type_specifier

let ast_node_pos = function
  | ASTExpression e -> e.loc
  | ASTStatement s -> s.loc
  | ASTVariable v -> v.location
  | ASTDeclaration d -> (
      match d with
      | Function f -> f.loc
      | Global d -> d.decl_loc
      | GlobalGroup gg -> gg.loc
      | FuncTypeDef f -> f.loc
      | DelegateDef f -> f.loc
      | StructDef s -> s.loc
      | Enum e -> e.loc)
  | ASTStructDecl d -> (
      match d with
      | AccessSpecifier _ -> dummy_location
      | MemberDecl d -> d.decl_loc
      | Constructor f -> f.loc
      | Destructor f -> f.loc
      | Method f -> f.loc)
  | ASTType t -> t.location

type jaf_struct = {
  name : string;
  index : int;
  members : (string, variable) Hashtbl.t;
}

let new_jaf_struct name index =
  { name; index; members = Hashtbl.create (module String) }

type library = { hll_name : string; functions : (string, fundecl) Hashtbl.t }

type context = {
  files : (string, string) Hashtbl.t;
  ain : Ain.t;
  debug_info : DebugInfo.t;
  globals : (string, variable) Hashtbl.t;
  structs : (string, jaf_struct) Hashtbl.t;
  functions : (string, fundecl) Hashtbl.t;
  functypes : (string, fundecl) Hashtbl.t;
  delegates : (string, fundecl) Hashtbl.t;
  libraries : (string, library) Hashtbl.t;
}

let context_from_ain ain =
  {
    files = Hashtbl.create (module String);
    ain;
    debug_info = DebugInfo.create ();
    globals = Hashtbl.create (module String);
    structs = Hashtbl.create (module String);
    functions = Hashtbl.create (module String);
    functypes = Hashtbl.create (module String);
    delegates = Hashtbl.create (module String);
    libraries = Hashtbl.create (module String);
  }

let find_hll_function ctx lib func =
  match Hashtbl.find ctx.libraries lib with
  | Some l -> Hashtbl.find l.functions func
  | None -> None

type resolved_name =
  | ResolvedLocal of variable
  | ResolvedGlobal of variable
  | ResolvedFunction of fundecl
  | ResolvedMember of jaf_struct * variable
  | ResolvedMethod of jaf_struct * fundecl
  | ResolvedLibrary of library
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

        method enter_function decl =
          self#push;
          current_function <- Some decl;
          List.iter decl.params ~f:self#push_var

        method leave_function =
          self#pop;
          current_function <- None

        method current_function = current_function

        method current_class =
          match current_function with
          | Some { class_name = Some name; class_index = Some index; _ } ->
              Some (Struct (name, index))
          | _ -> None

        method get_local name =
          List.find variables ~f:(fun v -> String.equal v.name name)

        method resolve name =
          let ctx_resolve ctx =
            match Hashtbl.find ctx.globals name with
            | Some g -> ResolvedGlobal g
            | None -> (
                match Hashtbl.find ctx.functions name with
                | Some f -> ResolvedFunction f
                | None -> (
                    match Hashtbl.find ctx.libraries name with
                    | Some l -> ResolvedLibrary l
                    | None -> UnresolvedName))
          in
          match name with
          | "system" -> ResolvedSystem
          | "assert" ->
              ResolvedBuiltin
                (Option.value_exn
                   (Bytecode.builtin_function_of_string "assert"))
          | _ -> (
              match self#get_local name with
              | Some v -> ResolvedLocal v
              | None -> (
                  match self#current_class with
                  | Some (Struct (s_name, _)) -> (
                      let s = Hashtbl.find_exn ctx.structs s_name in
                      match Hashtbl.find s.members name with
                      | Some v -> ResolvedMember (s, v)
                      | None -> (
                          match
                            Hashtbl.find ctx.functions (s_name ^ "@" ^ name)
                          with
                          | Some f -> ResolvedMethod (s, f)
                          | None -> ctx_resolve ctx))
                  | _ -> ctx_resolve ctx))

        method resolve_qualified sname name =
          match Hashtbl.find ctx.structs sname with
          | None -> UnresolvedName
          | Some s -> (
              match Hashtbl.find s.members name with
              | Some v -> ResolvedMember (s, v)
              | None -> UnresolvedName)
      end

    method visit_expression (e : expression) =
      match e.node with
      | ConstInt _ -> ()
      | ConstFloat _ -> ()
      | ConstChar _ -> ()
      | ConstString _ -> ()
      | Ident _ -> ()
      | FuncAddr _ -> ()
      | MemberAddr _ -> ()
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
          List.iter args ~f:(Option.iter ~f:self#visit_expression)
      | New t -> self#visit_type_specifier t
      | DummyRef (_, e) -> self#visit_expression e
      | This -> ()
      | Null -> ()

    method visit_vardecls (ds : vardecls) =
      self#visit_type_specifier ds.typespec;
      List.iter ds.vars ~f:(fun v ->
          (match v.kind with LocalVar -> environment#push_var v | _ -> ());
          self#visit_variable v)

    method visit_statement (s : statement) =
      match s.node with
      | EmptyStatement -> ()
      | Declarations ds -> self#visit_vardecls ds
      | Expression e -> self#visit_expression e
      | Compound stmts ->
          environment#push;
          List.iter stmts ~f:self#visit_statement;
          environment#pop
      | Label _ -> ()
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
      | Case e -> self#visit_expression e
      | Default -> ()
      | Return e -> Option.iter e ~f:self#visit_expression
      | Jump _ -> ()
      | Jumps e -> self#visit_expression e
      | Message _ -> ()
      | RefAssign (a, b) ->
          self#visit_expression a;
          self#visit_expression b
      | ObjSwap (a, b) ->
          self#visit_expression a;
          self#visit_expression b

    method visit_variable v =
      self#visit_type_specifier v.type_spec;
      List.iter v.array_dim ~f:self#visit_expression;
      Option.iter v.initval ~f:self#visit_expression

    method visit_fundecl f =
      self#visit_type_specifier f.return;
      List.iter f.params ~f:self#visit_variable;
      Option.iter f.body ~f:(fun body ->
          environment#enter_function f;
          List.iter ~f:self#visit_statement body;
          environment#leave_function)

    method visit_declaration d =
      match d with
      | Global ds -> self#visit_vardecls ds
      | GlobalGroup gg -> List.iter gg.vardecls ~f:self#visit_vardecls
      | Function f | FuncTypeDef f | DelegateDef f -> self#visit_fundecl f
      | StructDef s -> List.iter s.decls ~f:self#visit_struct_declaration
      | Enum enum ->
          let visit_enumval (_, expr) =
            Option.iter expr ~f:self#visit_expression
          in
          List.iter enum.values ~f:visit_enumval

    method visit_struct_declaration d =
      match d with
      | AccessSpecifier _ -> ()
      | MemberDecl ds -> self#visit_vardecls ds
      | Constructor f -> self#visit_fundecl f
      | Destructor f -> self#visit_fundecl f
      | Method f -> self#visit_fundecl f

    method visit_type_specifier (_t : type_specifier) = ()
    method visit_toplevel decls = List.iter decls ~f:self#visit_declaration
  end

let unary_op_to_string op =
  match op with
  | UPlus -> "+"
  | UMinus -> "-"
  | LogNot -> "!"
  | BitNot -> "~"
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
  | EqAssign | CharAssign -> "="
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

let is_numeric = function Int | Bool | LongInt | Float -> true | _ -> false

let rec jaf_type_to_string = function
  | Untyped -> "untyped"
  | Unresolved s -> "Unresolved<" ^ s ^ ">"
  | Void -> "void"
  | Int -> "int"
  | LongInt -> "lint"
  | Bool -> "bool"
  | Float -> "float"
  | String -> "string"
  | Struct (s, _) | FuncType (Some (s, _)) | Delegate (Some (s, _, _)) -> s
  | FuncType None -> "unknown_functype"
  | Delegate None -> "unknown_functype"
  | Ref t -> "ref " ^ jaf_type_to_string t
  | Array t -> "array<" ^ jaf_type_to_string t ^ ">" (* TODO: rank *)
  | Wrap t -> "wrap<" ^ jaf_type_to_string t ^ ">"
  | HLLParam -> "hll_param"
  | HLLFunc -> "hll_func"
  | IMainSystem -> "IMainSystem"
  | NullType -> "null"
  | TyFunction (args, ret) | TyMethod (args, ret) ->
      sprintf "%s(%s)" (jaf_type_to_string ret)
        (String.concat ~sep:", " (List.map ~f:jaf_type_to_string args))
  | MemberPtr (s, t) -> s ^ "::" ^ jaf_type_to_string t

let rec expr_to_string (e : expression) =
  let arglist_to_string args =
    let arg_to_string = Option.value_map ~default:"" ~f:expr_to_string in
    "(" ^ String.concat ~sep:", " (List.map ~f:arg_to_string args) ^ ")"
  in
  match e.node with
  | ConstInt i -> Int.to_string i
  | ConstFloat f -> Float.to_string f
  | ConstChar s -> sprintf "'%s'" s
  | ConstString s -> sprintf "\"%s\"" s
  | Ident (s, _) -> s
  | FuncAddr (s, _) -> "&" ^ s
  | MemberAddr (sname, name, _) -> sprintf "&%s::%s" sname name
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
  | Cast (t, e) -> sprintf "(%s)%s" (jaf_type_to_string t) (expr_to_string e)
  | Subscript (e, i) -> sprintf "%s[%s]" (expr_to_string e) (expr_to_string i)
  | Member (e, s, _) -> sprintf "%s.%s" (expr_to_string e) s
  | Call (f, args, _) ->
      sprintf "%s%s" (expr_to_string f) (arglist_to_string args)
  | New ts -> sprintf "new %s" (jaf_type_to_string ts.ty)
  | DummyRef (_, e) -> expr_to_string e
  | This -> "this"
  | Null -> "NULL"

let rec stmt_to_string (stmt : statement) =
  match stmt.node with
  | EmptyStatement -> ";"
  | Declarations ds -> vardecls_to_string ds
  | Expression e -> expr_to_string e ^ ";"
  | Compound stmts ->
      stmts |> List.map ~f:stmt_to_string |> List.fold ~init:"" ~f:( ^ )
  | Label label -> sprintf "%s:" label
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
  | Case expr -> sprintf "case %s:" (expr_to_string expr)
  | Default -> "default:"
  | Return None -> "return;"
  | Return (Some e) -> sprintf "return %s;" (expr_to_string e)
  | Jump func -> sprintf "jump %s;" func
  | Jumps e -> sprintf "jumps %s;" (expr_to_string e)
  | Message msg -> sprintf "'%s'" msg
  | RefAssign (dst, src) ->
      sprintf "%s <- %s;" (expr_to_string dst) (expr_to_string src)
  | ObjSwap (a, b) -> sprintf "%s <=> %s;" (expr_to_string a) (expr_to_string b)

and var_to_string' d =
  let dim_iter l r = l ^ sprintf "[%s]" (expr_to_string r) in
  let dims = List.fold d.array_dim ~init:"" ~f:dim_iter in
  let init =
    match d.initval with
    | None -> ""
    | Some e -> sprintf " = %s" (expr_to_string e)
  in
  sprintf "%s%s%s" dims d.name init

and var_to_string d =
  let t = jaf_type_to_string d.type_spec.ty in
  sprintf "%s %s;" t (var_to_string' d)

and vardecls_to_string (decls : vardecls) =
  let vars = List.map decls.vars ~f:var_to_string' |> String.concat ~sep:", " in
  sprintf "%s %s" (jaf_type_to_string decls.typespec.ty) vars

let params_to_string = function
  | [] -> "()"
  | p :: ps ->
      let rec loop result = function
        | [] -> result
        | p :: ps -> loop (sprintf "%s, %s" result (var_to_string' p)) ps
      in
      sprintf "(%s)" (loop (var_to_string' p) ps)

let body_to_string = function
  | None -> ";"
  | Some block ->
      List.fold (List.map block ~f:stmt_to_string) ~init:"" ~f:( ^ )
      |> sprintf " { %s }"

let sdecl_to_string = function
  | AccessSpecifier Public -> "public:"
  | AccessSpecifier Private -> "private:"
  | MemberDecl ds -> vardecls_to_string ds
  | Constructor d ->
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "%s%s%s" d.name params body
  | Destructor d ->
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "~%s%s%s" d.name params body
  | Method d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "%s %s%s%s" return d.name params body

let decl_to_string d =
  match d with
  | Global ds -> vardecls_to_string ds
  | GlobalGroup gg ->
      let body =
        List.fold (List.map gg.vardecls ~f:vardecls_to_string) ~init:"" ~f:( ^ )
      in
      sprintf "globalgroup %s { %s }" gg.name body
  | Function d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      let body = body_to_string d.body in
      sprintf "%s %s%s%s" return d.name params body
  | FuncTypeDef d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      sprintf "functype %s %s%s;" return d.name params
  | DelegateDef d ->
      let return = jaf_type_to_string d.return.ty in
      let params = params_to_string d.params in
      sprintf "delegate %s %s%s;" return d.name params
  | StructDef d ->
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
  | ASTStructDecl d -> sdecl_to_string d
  | ASTType t -> jaf_type_to_string t.ty

let rec jaf_to_ain_data_type = function
  | Untyped -> failwith "tried to convert Untyped to ain data type"
  | Unresolved s ->
      failwith ("tried to convert Unresolved to ain data type: " ^ s)
  | Ref _ -> failwith "tried to convert Ref to ain data type"
  | Void -> Ain.Type.Void
  | Int -> Ain.Type.Int
  | LongInt -> Ain.Type.LongInt
  | Bool -> Ain.Type.Bool
  | Float -> Ain.Type.Float
  | String -> Ain.Type.String
  | Struct (_, i) -> Ain.Type.Struct i
  | Array t -> Ain.Type.Array (Ain.Type.make (jaf_to_ain_data_type t))
  | Wrap t -> Ain.Type.Wrap (Ain.Type.make (jaf_to_ain_data_type t))
  | HLLParam -> Ain.Type.HLLParam
  | HLLFunc -> Ain.Type.HLLFunc
  | Delegate (Some (_, i, _)) -> Ain.Type.Delegate i
  | Delegate None -> Ain.Type.Delegate (-1)
  | FuncType (Some (_, i)) -> Ain.Type.FuncType i
  | FuncType None -> Ain.Type.FuncType (-1)
  | IMainSystem -> Ain.Type.IMainSystem
  | NullType -> Ain.Type.NullType
  | TyFunction _ -> Ain.Type.Function
  | TyMethod _ -> Ain.Type.Method
  | MemberPtr _ -> Ain.Type.Int (* slot number *)

and jaf_to_ain_type = function
  | Ref t -> Ain.Type.make ~is_ref:true (jaf_to_ain_data_type t)
  | t -> Ain.Type.make (jaf_to_ain_data_type t)

let rec data_type_to_jaf_type = function
  | Ain.Type.Void -> Void
  | Int -> Int
  | LongInt -> LongInt
  | Bool -> Bool
  | Float -> Float
  | String -> String
  | Struct i -> Struct ("", i)
  | Array t -> Array (ain_to_jaf_type t)
  | Wrap t -> Wrap (ain_to_jaf_type t)
  | HLLParam -> HLLParam
  | HLLFunc -> HLLFunc
  | Delegate i -> Delegate (Some ("", i, Untyped))
  | FuncType i -> FuncType (Some ("", i))
  | IMainSystem -> IMainSystem
  | t ->
      Printf.failwithf "cannot convert %s to jaf type"
        (Ain.Type.data_to_string t)
        ()

and ain_to_jaf_type t =
  if t.is_ref then Ref (data_type_to_jaf_type t.data)
  else data_type_to_jaf_type t.data

let jaf_to_ain_variables j_p =
  let rec convert_params (params : variable list) (result : Ain.Variable.t list)
      index =
    match params with
    | [] -> List.rev result
    | x :: xs ->
        let var =
          Ain.Variable.make ~index x.name (jaf_to_ain_type x.type_spec.ty)
        in
        if is_ref_scalar x.type_spec.ty then
          let void =
            Ain.Variable.make ~index:(index + 1) "<void>" (Ain.Type.make Void)
          in
          convert_params xs (void :: var :: result) (index + 2)
        else convert_params xs (var :: result) (index + 1)
  in
  convert_params j_p [] 0

let jaf_to_ain_function j_f (a_f : Ain.Function.t) =
  let vars = jaf_to_ain_variables j_f.params in
  {
    a_f with
    vars;
    nr_args = List.length vars;
    return_type = jaf_to_ain_type j_f.return.ty;
    is_label = j_f.is_label;
  }

let jaf_to_ain_struct j_s (a_s : Ain.Struct.t) =
  let members =
    List.filter_map j_s.decls ~f:(function
      | MemberDecl ds when not ds.is_const_decls -> Some ds.vars
      | _ -> None)
    |> List.concat |> jaf_to_ain_variables
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

let jaf_to_ain_functype j_f =
  let variables = jaf_to_ain_variables j_f.params in
  Ain.FunctionType.
    {
      name = j_f.name;
      index = Option.value_exn j_f.index;
      variables;
      nr_arguments = List.length variables;
      return_type = jaf_to_ain_type j_f.return.ty;
    }

let jaf_to_ain_hll_function j_f =
  let jaf_to_ain_hll_argument (param : variable) =
    Ain.Library.Argument.create param.name (jaf_to_ain_type param.type_spec.ty)
  in
  let return_type = jaf_to_ain_type j_f.return.ty in
  let arguments = List.map j_f.params ~f:jaf_to_ain_hll_argument in
  Ain.Library.Function.create j_f.name return_type arguments
