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
open Jaf
open CompileError

let rec type_equal (expected : Ain.Type.data) (actual : Ain.Type.data) =
  match (expected, actual) with
  | Void, _ ->
      true (* XXX: used for type-generic built-ins (e.g. Array.PushBack) *)
  | Int, (Int | Bool | LongInt) -> true
  | Bool, (Int | Bool | LongInt) -> true
  | LongInt, (Int | Bool | LongInt) -> true
  | Float, Float -> true
  | String, String -> true
  | Struct a, Struct b -> a = b
  | IMainSystem, IMainSystem -> true
  | FuncType a, FuncType b -> a = b
  | Delegate a, Delegate b -> a = b
  | (FuncType _ | Delegate _ | IMainSystem), NullType -> true
  | NullType, (FuncType _ | Delegate _ | IMainSystem | NullType) -> true
  | HLLFunc2, HLLFunc2 -> true
  | HLLParam, HLLParam -> true
  | Array a, Array b -> type_equal a.data b.data
  | Wrap a, Wrap b -> type_equal a.data b.data
  | Option a, Option b -> type_equal a.data b.data
  | Unknown87 a, Unknown87 b -> type_equal a.data b.data
  | IFace a, IFace b -> a = b
  | Enum2 a, Enum2 b -> a = b
  | Enum a, Enum b -> a = b
  | HLLFunc, HLLFunc -> true
  | Unknown98, Unknown98 -> true
  | IFaceWrap a, IFaceWrap b -> a = b
  | Function _, Function _ -> true
  | Method _, Method _ -> true
  | Int, _
  | Bool, _
  | LongInt, _
  | Float, _
  | String, _
  | Struct _, _
  | IMainSystem, _
  | FuncType _, _
  | Delegate _, _
  | HLLFunc2, _
  | HLLParam, _
  | Array _, _
  | Wrap _, _
  | Option _, _
  | Unknown87 _, _
  | IFace _, _
  | Enum2 _, _
  | Enum _, _
  | HLLFunc, _
  | Unknown98, _
  | IFaceWrap _, _
  | Function _, _
  | Method _, _
  | NullType, _ ->
      false

let type_castable (dst : data_type) (src : Ain.Type.data) =
  match (dst, src) with
  (* FIXME: cast to void should be allowed *)
  | Void, _ -> compiler_bug "type checker cast to void type" None
  | (Int | Bool | Float), (Int | Bool | Float) -> true
  | _ -> false

let type_check parent expected actual =
  match actual.valuetype with
  | None -> compiler_bug "tried to type check untyped expression" (Some parent)
  | Some a_t ->
      if not (type_equal expected a_t.data) then
        data_type_error expected (Some actual) parent

let type_check_numeric parent actual =
  match actual.valuetype with
  | Some { data = Int | Bool | Float; _ } -> ()
  | Some _ -> data_type_error Int (Some actual) parent
  | None -> compiler_bug "tried to type check untyped expression" (Some parent)

let type_check_struct parent actual =
  match actual.valuetype with
  | Some { data = Struct i; _ } -> i
  | Some _ -> data_type_error (Struct 0) (Some actual) parent
  | None -> compiler_bug "tried to type check untyped expression" (Some parent)

class type_analyze_visitor ctx =
  object (self)
    inherit ivisitor ctx as super

    (* an lvalue is an expression which denotes a location that can be assigned to/referenced *)
    method check_lvalue (e : expression) (parent : ast_node) =
      let check_lvalue_type = function
        | Ain.Type.Function _ -> not_an_lvalue_error e parent
        | _ -> ()
      in
      match e.node with
      | Ident (_, _) -> check_lvalue_type (Option.value_exn e.valuetype).data
      | Member (_, _, _) ->
          check_lvalue_type (Option.value_exn e.valuetype).data
      | Subscript (_, _) -> ()
      | New (_, _, _) -> ()
      | _ -> not_an_lvalue_error e parent

    method check_delegate_compatible parent dg_i expr =
      match Option.value_exn expr.valuetype with
      | { data = Ain.Type.Method f_i; is_ref = true } ->
          let dg = Ain.get_delegate_by_index ctx.ain dg_i in
          let f = Ain.get_function_by_index ctx.ain f_i in
          if not (Ain.FunctionType.function_compatible dg f) then
            data_type_error (Ain.Type.Delegate dg_i) (Some expr) parent
      | { data = Ain.Type.Delegate no; _ } ->
          if not (phys_equal dg_i no) then
            data_type_error (Ain.Type.Delegate dg_i) (Some expr) parent
      | _ -> ref_type_error (Ain.Type.Method (-1)) (Some expr) parent

    method check_assign parent t rhs =
      match t with
      (*
       * Assigning to a functype or delegate variable is special.
       * The RHS should be an expression like &foo, which has type
       * 'ref function'. This is then converted into the declared
       * functype of the variable (if the prototypes match).
       *)
      | Ain.Type.FuncType ft_i -> (
          match Option.value_exn rhs.valuetype with
          | { data = Ain.Type.Function f_i; is_ref = true } ->
              let ft = Ain.get_functype_by_index ctx.ain ft_i in
              let f = Ain.get_function_by_index ctx.ain f_i in
              if not (Ain.FunctionType.function_compatible ft f) then
                data_type_error (Ain.Type.FuncType ft_i) (Some rhs) parent
          | _ -> ref_type_error (Ain.Type.Function (-1)) (Some rhs) parent)
      | Ain.Type.Delegate dg_i -> self#check_delegate_compatible parent dg_i rhs
      | _ -> type_check parent t rhs

    method! visit_expression expr =
      super#visit_expression expr;
      (* convenience functions which always pass parent expression *)
      let check = type_check (ASTExpression expr) in
      let check_numeric = type_check_numeric (ASTExpression expr) in
      let check_struct = type_check_struct (ASTExpression expr) in
      let check_expr a b = check (Option.value_exn a.valuetype).data b in
      (* check function call arguments *)
      let check_call (f : Ain.Function.t) args =
        let params = Ain.Function.logical_parameters f in
        let nr_params = List.length params in
        if not (nr_params = List.length args) then
          arity_error f args (ASTExpression expr)
        else if nr_params > 0 then
          let check_arg a (v : Ain.Variable.t) = check v.value_type.data a in
          List.iter2_exn args params ~f:check_arg
      in
      let set_valuetype spec = expr.valuetype <- Some (jaf_to_ain_type spec) in
      match expr.node with
      | ConstInt _ -> expr.valuetype <- Some (Ain.Type.make Int)
      | ConstFloat _ -> expr.valuetype <- Some (Ain.Type.make Float)
      | ConstChar _ -> expr.valuetype <- Some (Ain.Type.make Int)
      | ConstString _ -> expr.valuetype <- Some (Ain.Type.make String)
      | Ident (name, _) -> (
          match environment#resolve name with
          | ResolvedLocal v ->
              expr.node <- Ident (name, Some (LocalVariable (-1)));
              set_valuetype { data = v.type_spec.data; is_ref = false }
          | ResolvedConstant v ->
              expr.node <- Ident (name, Some GlobalConstant);
              set_valuetype { data = v.type_spec.data; is_ref = false }
          | ResolvedGlobal g ->
              expr.node <- Ident (name, Some (GlobalVariable g.index));
              expr.valuetype <- Some g.value_type
          | ResolvedFunction i ->
              expr.node <- Ident (name, Some (FunctionName i));
              expr.valuetype <- Some (Ain.Type.make (Function i))
          | ResolvedLibrary i ->
              expr.node <- Ident (name, Some (HLLName i));
              expr.valuetype <- Some (Ain.Type.make Void)
          | ResolvedSystem ->
              expr.node <- Ident ("system", Some System);
              expr.valuetype <- Some (Ain.Type.make Void)
          | ResolvedBuiltin builtin ->
              expr.node <- Ident (name, Some (BuiltinFunction builtin));
              expr.valuetype <- Some (Ain.Type.make Void)
          | UnresolvedName -> undefined_variable_error name (ASTExpression expr)
          )
      | Unary (op, e) -> (
          match op with
          | UPlus | UMinus | PreInc | PreDec | PostInc | PostDec ->
              check_numeric e;
              expr.valuetype <- Some (Option.value_exn e.valuetype)
          | LogNot | BitNot ->
              check Int e;
              expr.valuetype <- Some (Option.value_exn e.valuetype)
          | AddrOf -> (
              match (Option.value_exn e.valuetype).data with
              | Function i ->
                  expr.valuetype <-
                    Some (Ain.Type.make ~is_ref:true (Function i))
              | Method i ->
                  expr.valuetype <- Some (Ain.Type.make ~is_ref:true (Method i))
              | _ ->
                  data_type_error (Function (-1)) (Some e) (ASTExpression expr))
          )
      | Binary (op, a, b) -> (
          match op with
          | Plus ->
              (match (Option.value_exn a.valuetype).data with
              | String -> check String b
              | _ ->
                  check_numeric a;
                  check_numeric b;
                  (* TODO: allow coercion *)
                  check_expr a b);
              expr.valuetype <- a.valuetype
          | Minus | Times | Divide ->
              check_numeric a;
              check_numeric b;
              (* TODO: allow coercion *)
              check_expr a b;
              expr.valuetype <- a.valuetype
          | LogOr | LogAnd | BitOr | BitXor | BitAnd | LShift | RShift ->
              check Int a;
              check Int b;
              expr.valuetype <- a.valuetype
          | Modulo ->
              (match (Option.value_exn a.valuetype).data with
              | String -> (
                  (* TODO: check type matches format specifier if format string is a literal *)
                  match (Option.value_exn b.valuetype).data with
                  | Int | Float | Bool | LongInt | String -> ()
                  | _ -> data_type_error Int (Some b) (ASTExpression expr))
              | Int | Bool | LongInt -> check Int b
              | _ -> data_type_error Int (Some a) (ASTExpression expr));
              expr.valuetype <- a.valuetype
          | Equal | NEqual | LT | GT | LTE | GTE ->
              (match (Option.value_exn a.valuetype).data with
              | String -> check String b
              | _ ->
                  check_numeric a;
                  check_numeric b;
                  (* TODO: allow coercion *)
                  check_expr a b);
              expr.valuetype <- Some (Ain.Type.make Int)
          | RefEqual | RefNEqual ->
              (match
                 ( (Option.value_exn a.valuetype).is_ref,
                   (Option.value_exn b.valuetype).is_ref )
               with
              | true, true -> check_expr a b
              | false, _ -> ref_type_error Void (Some a) (ASTExpression expr)
              | _, false -> ref_type_error Void (Some b) (ASTExpression expr));
              expr.valuetype <- Some (Ain.Type.make Int))
      | Assign (op, lhs, rhs) -> (
          self#check_lvalue lhs (ASTExpression expr);
          let lhs_type = (Option.value_exn lhs.valuetype).data in
          let rhs_type = (Option.value_exn rhs.valuetype).data in
          (match (lhs_type, op) with
          | _, EqAssign -> self#check_assign (ASTExpression expr) lhs_type rhs
          | String, PlusAssign -> check String rhs
          | Delegate dg_i, (PlusAssign | MinusAssign) ->
              self#check_delegate_compatible (ASTExpression expr) dg_i rhs
          | _, (PlusAssign | MinusAssign | TimesAssign | DivideAssign) ->
              check_numeric lhs;
              check_numeric rhs;
              (* TODO: allow coercion *)
              check_expr lhs rhs
          | ( _,
              ( ModuloAssign | OrAssign | XorAssign | AndAssign | LShiftAssign
              | RShiftAssign ) ) ->
              check Int lhs;
              check Int rhs);
          (* XXX: Nothing is left on stack after assigning method to delegate *)
          match (lhs_type, rhs_type) with
          | Delegate _, Method _ -> expr.valuetype <- Some (Ain.Type.make Void)
          | _ -> expr.valuetype <- lhs.valuetype)
      | Seq (_, e) -> expr.valuetype <- e.valuetype
      | Ternary (test, con, alt) ->
          check Int test;
          check_expr con alt;
          expr.valuetype <- con.valuetype
      | Cast (t, e) ->
          if not (type_castable t (Option.value_exn e.valuetype).data) then
            data_type_error (jaf_to_ain_data_type t) (Some e)
              (ASTExpression expr);
          set_valuetype { data = t; is_ref = false }
      | Subscript (obj, i) -> (
          check Int i;
          match (Option.value_exn obj.valuetype).data with
          | Array t -> expr.valuetype <- Some t
          | String -> expr.valuetype <- Some (Ain.Type.make Int)
          | _ ->
              (* FIXME: Expected type here is array<?>|string *)
              let array_type = { data = Void; is_ref = false } in
              let expected = Array array_type in
              data_type_error
                (jaf_to_ain_data_type expected)
                (Some obj) (ASTExpression expr))
      (* system function *)
      | Member (({ node = Ident (_, Some System); _ } as e), syscall_name, _)
        -> (
          match Bytecode.syscall_of_string syscall_name with
          | Some sys ->
              expr.node <- Member (e, syscall_name, Some (SystemFunction sys));
              expr.valuetype <- Some (Ain.Type.make (Function 0))
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error ("system." ^ syscall_name)
                (ASTExpression expr))
      (* HLL function *)
      | Member
          ( ({ node = Ident (lib_name, Some (HLLName lib_no)); _ } as e),
            fun_name,
            _ ) -> (
          match Ain.get_library_function_index ctx.ain lib_no fun_name with
          | Some fun_no ->
              expr.node <-
                Member (e, fun_name, Some (HLLFunction (lib_no, fun_no)));
              expr.valuetype <- Some (Ain.Type.make (Function 0))
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error
                (lib_name ^ "." ^ fun_name)
                (ASTExpression expr))
      (* built-in methods *)
      | Member
          ( ({
               valuetype =
                 Some
                   {
                     data = (Int | Float | String | Array _ | Delegate _) as t;
                     _;
                   };
               _;
             } as e),
            name,
            _ ) -> (
          match Bytecode.builtin_of_string t name with
          | Some builtin ->
              expr.node <- Member (e, name, Some (BuiltinMethod builtin));
              expr.valuetype <- Some (Ain.Type.make (Function 0))
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error
                (Ain.Type.data_to_string t ^ name)
                (ASTExpression expr))
      (* member variable OR method *)
      | Member (obj, member_name, _) -> (
          let struc = Ain.get_struct_by_index ctx.ain (check_struct obj) in
          let check_member _ (m : Ain.Variable.t) =
            String.equal m.name member_name
          in
          match List.findi struc.members ~f:check_member with
          | Some (_, member) ->
              expr.node <-
                Member
                  ( obj,
                    member_name,
                    Some (ClassVariable (struc.index, member.index)) );
              expr.valuetype <- Some member.value_type
          | None -> (
              let fun_name = struc.name ^ "@" ^ member_name in
              match Ain.get_function ctx.ain fun_name with
              | Some f ->
                  expr.node <-
                    Member
                      ( obj,
                        member_name,
                        Some (ClassMethod (struc.index, f.index)) );
                  expr.valuetype <- Some (Ain.Type.make (Method f.index))
              | None ->
                  (* TODO: separate error type for this? *)
                  undefined_variable_error
                    (struc.name ^ "." ^ member_name)
                    (ASTExpression expr)))
      (* regular function call *)
      | Call (({ node = Ident (_, Some (FunctionName fno)); _ } as e), args, _)
        ->
          let f = Ain.get_function_by_index ctx.ain fno in
          check_call f args;
          expr.node <- Call (e, args, Some (FunctionCall fno));
          expr.valuetype <- Some f.return_type
      (* built-in function call *)
      | Call
          ( ({ node = Ident (_, Some (BuiltinFunction builtin)); _ } as e),
            args,
            _ ) ->
          let f = Bytecode.function_of_builtin builtin in
          check_call f args;
          expr.node <- Call (e, args, Some (BuiltinCall builtin));
          expr.valuetype <- Some f.return_type
      (* method call *)
      | Call
          ( ({ node = Member (_, _, Some (ClassMethod (sno, mno))); _ } as e),
            args,
            _ ) ->
          let f = Ain.get_function_by_index ctx.ain mno in
          check_call f args;
          expr.node <- Call (e, args, Some (MethodCall (sno, mno)));
          expr.valuetype <- Some f.return_type
      (* HLL call *)
      | Call
          ( ({ node = Member (_, _, Some (HLLFunction (lib_no, fun_no))); _ } as
             e),
            args,
            _ ) ->
          let f = Ain.function_of_hll_function_index ctx.ain lib_no fun_no in
          check_call f args;
          expr.node <- Call (e, args, Some (HLLCall (lib_no, fun_no, -1)));
          expr.valuetype <- Some f.return_type
      (* system call *)
      | Call
          ( ({ node = Member (_, _, Some (SystemFunction sys)); _ } as e),
            args,
            _ ) ->
          let f = Bytecode.function_of_syscall sys in
          check_call f args;
          expr.node <- Call (e, args, Some (SystemCall sys));
          expr.valuetype <- Some f.return_type
      (* built-in method call *)
      | Call
          ( ({ node = Member (_, _, Some (BuiltinMethod builtin)); _ } as e),
            args,
            _ ) ->
          (* TODO: rewrite to HLL call for 11+ (?) *)
          if Ain.version_gte ctx.ain (11, 0) then
            compile_error "ain v11+ built-ins not implemented"
              (ASTExpression expr);
          let f = Bytecode.function_of_builtin builtin in
          (* TODO: properly check type-generic arguments based on object type *)
          check_call f args;
          expr.node <- Call (e, args, Some (BuiltinCall builtin));
          expr.valuetype <- Some f.return_type
      (* functype/delegate call *)
      | Call (e, args, _) -> (
          match (Option.value_exn e.valuetype).data with
          | FuncType no ->
              let f = Ain.function_of_functype_index ctx.ain no in
              check_call f args;
              expr.node <- Call (e, args, Some (FuncTypeCall no));
              expr.valuetype <- Some f.return_type
          | Delegate no ->
              let f = Ain.function_of_delegate_index ctx.ain no in
              check_call f args;
              expr.node <- Call (e, args, Some (DelegateCall no));
              expr.valuetype <- Some f.return_type
          | _ ->
              data_type_error (Ain.Type.FuncType (-1)) (Some e)
                (ASTExpression expr))
      | New (t, args, _) -> (
          match t with
          | Struct (_, i) ->
              (* TODO: look up the correct constructor for given arguments *)
              (match (Ain.get_struct_by_index ctx.ain i).constructor with
              | -1 ->
                  if not (List.length args = 0) then
                    (* TODO: signal error properly here *)
                    compile_error "Arguments provided to default constructor"
                      (ASTExpression expr)
              | no ->
                  let ctor = Ain.get_function_by_index ctx.ain no in
                  check_call ctor args);
              set_valuetype { data = t; is_ref = false }
          | _ -> data_type_error (Struct (-1)) None (ASTExpression expr))
      | This -> (
          match environment#current_class with
          | Some i -> expr.valuetype <- Some (Ain.Type.make (Struct i))
          | None ->
              (* TODO: separate error type for this? *)
              undefined_variable_error "this" (ASTExpression expr))
      | Null -> expr.valuetype <- Some (Ain.Type.make NullType)

    method! visit_statement stmt =
      (* rewrite character constants at statement-level as messages *)
      (match stmt.node with
      | Expression { node = ConstChar msg; _ } ->
          stmt.node <- MessageCall (msg, None, None)
      | _ -> ());
      super#visit_statement stmt;
      match stmt.node with
      | EmptyStatement -> ()
      | Declarations _ -> ()
      | Expression _ -> ()
      | Compound _ -> ()
      | Labeled (_, _) -> ()
      | If (test, _, _) | While (test, _) | DoWhile (test, _) ->
          type_check (ASTStatement stmt) Int test
      | For (_, Some test, _, _) -> type_check (ASTStatement stmt) Int test
      | For (_, None, _, _) -> ()
      | Goto _ -> ()
      | Continue -> ()
      | Break -> ()
      | Switch (expr, _) ->
          (* TODO: string switch *)
          type_check (ASTStatement stmt) Int expr
      | Case (expr, _) ->
          (* TODO: string switch *)
          type_check (ASTStatement stmt) Int expr
      | Default _ -> ()
      | Return (Some e) -> (
          match environment#current_function with
          | None ->
              compiler_bug "return statement outside of function"
                (Some (ASTStatement stmt))
          | Some f ->
              type_check (ASTStatement stmt)
                (jaf_to_ain_data_type f.return.data)
                e)
      | Return None -> (
          match environment#current_function with
          | None ->
              compiler_bug "return statement outside of function"
                (Some (ASTStatement stmt))
          | Some f -> (
              match f.return.data with
              | Void -> ()
              | _ ->
                  data_type_error
                    (jaf_to_ain_data_type f.return.data)
                    None (ASTStatement stmt)))
      | MessageCall (msg, f_name, _) -> (
          match f_name with
          | Some name -> (
              match Ain.get_function ctx.ain name with
              | Some f ->
                  if f.nr_args > 0 then arity_error f [] (ASTStatement stmt);
                  stmt.node <- MessageCall (msg, f_name, Some f.index)
              | None -> undefined_variable_error name (ASTStatement stmt))
          | None -> ())
      | RefAssign (lhs, rhs) -> (
          (* rhs must be an lvalue in order to create a reference to it *)
          self#check_lvalue rhs (ASTStatement stmt);
          (* check that lhs is a reference variable of the appropriate type *)
          match lhs.node with
          | Ident (name, _) -> (
              match environment#get_local name with
              | Some v ->
                  if v.type_spec.is_ref then
                    type_check (ASTStatement stmt)
                      (Option.value_exn lhs.valuetype).data rhs
                  else
                    ref_type_error (Option.value_exn rhs.valuetype).data
                      (Some lhs) (ASTStatement stmt)
              | None -> undefined_variable_error name (ASTStatement stmt))
          | _ ->
              (* FIXME? this isn't really a _type_ error *)
              ref_type_error (Option.value_exn rhs.valuetype).data (Some lhs)
                (ASTStatement stmt))
      | ObjSwap (lhs, rhs) ->
          self#check_lvalue lhs (ASTStatement stmt);
          self#check_lvalue rhs (ASTStatement stmt);
          (* FIXME: error if the type is ref or unsupported type *)
          type_check (ASTStatement stmt) (Option.value_exn lhs.valuetype).data
            rhs

    method visit_variable var =
      let rec calculate_array_rank (t : type_specifier) =
        match t.data with
        | Array sub_t -> 1 + calculate_array_rank sub_t
        | _ -> 0
      in
      let rank = calculate_array_rank var.type_spec in
      let nr_dims = List.length var.array_dim in
      (* Only one array dimension may be specified in ain v11+ *)
      if nr_dims > 1 && Ain.version_gte ctx.ain (11, 0) then
        compile_error "Multiple array dimensions specified for ain v11+"
          (ASTVariable var);
      (* Check that there is no initializer if array has explicit dimensions *)
      if nr_dims > 0 && Option.is_some var.initval then
        compile_error "Initializer provided for array with explicit dimensions"
          (ASTVariable var);
      (* Check that number of dims matches rank of array *)
      if nr_dims > 0 && not (nr_dims = rank) then
        compile_error "Number of array dimensions does not match array rank"
          (ASTVariable var);
      (* Check that array dims are integers *)
      List.iter var.array_dim ~f:(fun e -> type_check (ASTVariable var) Int e);
      (* Check initval matches declared type *)
      match var.initval with
      | Some expr ->
          if var.type_spec.is_ref then
            compile_error "Initial value for ref type not implemented"
              (ASTVariable var)
          else
            self#check_assign (ASTVariable var)
              (jaf_to_ain_data_type var.type_spec.data)
              expr
      | None -> ()

    method! visit_local_variable var =
      super#visit_local_variable var;
      self#visit_variable var

    method! visit_declaration decl =
      super#visit_declaration decl;
      match decl with Global g -> self#visit_variable g | _ -> ()

    method! visit_fundecl f =
      super#visit_fundecl f;
      if String.equal f.name "main" then
        match (f.return, f.params) with
        | { data = Int; is_ref = false }, [] ->
            Ain.set_main_function ctx.ain (Option.value_exn f.index)
        | _ ->
            compile_error "Invalid declaration of 'main' function"
              (ASTDeclaration (Function f))
      else if String.equal f.name "message" then
        match f.return with
        | { data = Void; is_ref = false } -> (
            match List.map f.params ~f:(fun v -> v.type_spec) with
            | [
             { data = Int; is_ref = false };
             { data = Int; is_ref = false };
             { data = String; is_ref = false };
            ] ->
                Ain.set_message_function ctx.ain (Option.value_exn f.index)
            | _ ->
                compile_error "Invalid declaration of 'message' function"
                  (ASTDeclaration (Function f)))
        | _ ->
            compile_error "invalid declaration of 'message' function"
              (ASTDeclaration (Function f))
  end

let check_types ctx decls = (new type_analyze_visitor ctx)#visit_toplevel decls
