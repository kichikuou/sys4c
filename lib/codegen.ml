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
open Jaf
open Bytecode
open CompileError

type cflow_type = CFlowLoop of int | CFlowSwitch of Ain.Switch.t
type cflow_stmt = { kind : cflow_type; mutable break_addrs : int list }

type scope = {
  mutable vars : Ain.Variable.t list;
  mutable labels : (string * int) list;
  mutable gotos : (string * int * statement) list;
}

let is_variable_ref = function
  | Ident _ | Member (_, _, ClassVariable _) | Subscript _ -> true
  | _ -> false

class jaf_compiler ain =
  object (self)
    (* The function currently being compiled. *)
    val mutable current_function : Ain.Function.t option = None

    (* The bytecode output buffer. *)
    val mutable buffer = CBuffer.create 2048

    (* Address of the start of the current buffer. *)
    val mutable start_address : int = 0

    (* Current address within the code section. *)
    val mutable current_address : int = 0

    (* The currently active control flow constructs. *)
    val cflow_stmts = Stack.create ()

    (* The currentl active scopes. *)
    val scopes = Stack.create ()

    (** Begin a scope. Variables created within a scope are deleted when the
      scope ends. *)
    method start_scope =
      Stack.push scopes { vars = []; labels = []; gotos = [] }

    (** End a scope. Deletes variable created within the scope. *)
    method end_scope =
      let scope = Stack.pop_exn scopes in
      (* update goto addresses *)
      let unresolved =
        List.filter scope.gotos ~f:(fun (name, addr_loc, _) ->
            match
              List.findi scope.labels ~f:(fun _ (label_name, _) ->
                  String.equal name label_name)
            with
            | Some (_, (_, addr)) ->
                self#write_address_at addr_loc addr;
                false
            | None -> true)
      in
      (* unresolved gotos are moved to parent scope *)
      (match (Stack.top scopes, unresolved) with
      | _, [] -> ()
      | None, (_, _, stmt) :: _ ->
          compile_error "Unresolved label" (ASTStatement stmt)
      | Some parent, unresolved ->
          parent.gotos <- List.append parent.gotos unresolved);
      (* delete scope-local variables *)
      (* NOTE: Variables are deleted automatically by the VM upon function
               return. This code is emitted only to ensure that destructors are
               called at the correct time; hence function-scoped variables need
               not be deleted here. *)
      match Stack.top scopes with
      | None -> ()
      | Some _ -> List.iter scope.vars ~f:self#compile_delete_var

    (** Add a variable to the current scope. *)
    method scope_add_var v =
      match Stack.top scopes with
      | Some scope -> scope.vars <- v :: scope.vars
      | None -> compiler_bug "tried to add variable to null scope" None

    (** Add a label to the current scope. *)
    method scope_add_label name =
      let scope = Stack.top_exn scopes in
      scope.labels <- (name, current_address) :: scope.labels

    (** Add a goto address location to the current scope *)
    method scope_add_goto name addr_loc stmt =
      let scope = Stack.top_exn scopes in
      scope.gotos <- (name, addr_loc, stmt) :: scope.gotos

    (** Begin a loop. *)
    method start_loop addr =
      Stack.push cflow_stmts { kind = CFlowLoop addr; break_addrs = [] }

    (** Begin a switch statement. *)
    method start_switch =
      let switch = Ain.add_switch ain in
      Stack.push cflow_stmts { kind = CFlowSwitch switch; break_addrs = [] };
      switch.index

    (** End the current control flow construct. Updates 'break' addresses. *)
    method end_cflow_stmt =
      let stmt = Stack.pop_exn cflow_stmts in
      List.iter stmt.break_addrs ~f:(fun addr ->
          self#write_address_at addr current_address)

    (** End the current loop. Updates 'break' addresses. *)
    method end_loop =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowLoop _; _ } -> ()
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    (** End the current switch statement. Updates 'break' addresses. *)
    method end_switch =
      (match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> Ain.write_switch ain switch
      | _ -> compiler_bug "Mismatched start/end of control flow construct" None);
      self#end_cflow_stmt

    method add_switch_case value node =
      let (switch : Ain.Switch.t) = self#current_switch node in
      switch.cases <-
        List.append switch.cases [ (Int32.of_int_exn value, current_address) ]

    method set_switch_default node =
      let switch = self#current_switch node in
      switch.default_address <- current_address

    (** Retrieves the continue address for the current loop (i.e. the address
      that 'continue' statements should jump to). *)
    method get_continue_addr node =
      let rec get_first_continue = function
        | { kind = CFlowLoop addr; _ } :: _ -> addr
        | _ :: rest -> get_first_continue rest
        | [] -> compile_error "'continue' statement outside of loop" node
      in
      match Stack.top cflow_stmts with
      | Some { kind = CFlowLoop addr; _ } -> addr
      | Some { kind = CFlowSwitch _; _ } ->
          get_first_continue (Stack.to_list cflow_stmts)
      | _ -> compile_error "'continue' statement outside of loop" node

    (** Retrieves the index for the current switch statement. *)
    method current_switch node =
      match Stack.top cflow_stmts with
      | Some { kind = CFlowSwitch switch; _ } -> switch
      | _ -> compile_error "switch case outside of switch statement" node

    (** Push the location of a 32-bit integer that should be updated to the
      address of the current scope's end point. *)
    method push_break_addr addr node =
      match Stack.top cflow_stmts with
      | Some stmt -> stmt.break_addrs <- addr :: stmt.break_addrs
      | None -> compile_error "'break' statement outside of loop" node

    method compile_CALLHLL lib_name fun_name t parent =
      match Ain.get_library_index ain lib_name with
      | Some lib_no -> (
          match Ain.get_library_function_index ain lib_no fun_name with
          | Some fun_no -> self#write_instruction3 CALLHLL lib_no fun_no t
          | None -> compile_error "No HLL function found for built-in" parent)
      | None -> compile_error "No HLL library found for built-in" parent

    method write_instruction0 op =
      CBuffer.write_int16 buffer (int_of_opcode op);
      current_address <- current_address + 2

    method write_instruction1 op arg0 =
      match (Ain.version_lt ain (8, 0), op) with
      | true, S_MOD ->
          self#write_instruction1 PUSH arg0;
          self#write_instruction0 S_MOD
      | _ ->
          CBuffer.write_int16 buffer (int_of_opcode op);
          CBuffer.write_int32 buffer arg0;
          current_address <- current_address + 6

    method write_instruction1_float op arg0 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_float buffer arg0;
      current_address <- current_address + 6

    method write_instruction2 op arg0 arg1 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      current_address <- current_address + 10

    method write_instruction3 op arg0 arg1 arg2 =
      CBuffer.write_int16 buffer (int_of_opcode op);
      CBuffer.write_int32 buffer arg0;
      CBuffer.write_int32 buffer arg1;
      CBuffer.write_int32 buffer arg2;
      current_address <- current_address + 14

    method write_address_at dst addr =
      CBuffer.write_int32_at buffer (dst - start_address) addr

    method write_buffer =
      if current_address > start_address then (
        Ain.append_bytecode ain buffer;
        CBuffer.clear buffer;
        start_address <- current_address)

    method get_local i =
      match current_function with
      | Some f -> List.nth_exn f.vars i
      | None -> compiler_bug "get_local outside of function" None

    method compile_lock_peek =
      if Ain.version_lt ain (6, 0) then (
        self#write_instruction1 CALLSYS (int_of_syscall LockPeek);
        self#write_instruction0 POP)

    method compile_unlock_peek =
      if Ain.version_lt ain (6, 0) then (
        self#write_instruction1 CALLSYS (int_of_syscall UnlockPeek);
        self#write_instruction0 POP)

    method compile_delete_var (v : Ain.Variable.t) =
      match v.value_type.data with
      | Struct _ -> self#write_instruction1 SH_LOCALDELETE v.index
      | Array _ ->
          self#compile_local_ref v.index;
          self#write_instruction0 A_FREE
      | _ -> ()

    (** Emit the code to put the value of a variable onto the stack (including
      member variables and array elements). Assumes a page + page-index is
      already on the stack. *)
    method compile_dereference (t : Ain.Type.t) =
      match t.data with
      | Int | Float | Bool | LongInt | FuncType _ ->
          if t.is_ref then self#write_instruction0 REFREF;
          self#write_instruction0 REF
      | String -> self#write_instruction0 S_REF
      | Array _ ->
          self#write_instruction0 REF;
          self#write_instruction0 A_REF
      | Struct no -> self#write_instruction1 SR_REF no
      | Delegate _ ->
          self#write_instruction0 REF;
          self#write_instruction0 DG_COPY
      | Void | IMainSystem | HLLFunc2 | HLLParam | Wrap _ | Option _
      | Unknown87 _ | IFace _ | Enum2 _ | Enum _ | HLLFunc | Unknown98
      | IFaceWrap _ | Function _ | Method _ | NullType ->
          compiler_bug "dereference not supported for type" None

    method compile_local_ref i =
      self#write_instruction0 PUSHLOCALPAGE;
      self#write_instruction1 PUSH i

    method compile_global_ref i =
      self#write_instruction0 PUSHGLOBALPAGE;
      self#write_instruction1 PUSH i

    method compile_identifier_ref id_type =
      match id_type with
      | LocalVariable i -> self#compile_local_ref (self#get_local i).index
      | GlobalVariable i ->
          self#compile_global_ref (Ain.get_global_by_index ain i).index
      | _ -> compiler_bug "Invalid identifier type" None

    method compile_variable_ref (e : expression) =
      match e.node with
      | Ident (_, id_type) -> self#compile_identifier_ref id_type
      | Member (e, _, ClassVariable (_, member_no)) ->
          self#compile_lvalue e;
          self#write_instruction1 PUSH member_no
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          self#compile_expression index
      | _ -> compiler_bug "Invalid variable ref" (Some (ASTExpression e))

    method compile_delete_ref ty =
      self#write_instruction0 DUP2;
      if is_ref_scalar ty then (
        self#write_instruction0 REFREF;
        self#write_instruction0 POP)
      else self#write_instruction0 REF;
      self#write_instruction0 DELETE

    (** Emit the code to put a location (variable, struct member, or array
      element) onto the stack, e.g. to prepare for an assignment or to pass
      a variable by reference. *)
    method compile_lvalue (e : expression) =
      let compile_lvalue_after (t : Ain.Type.t) =
        if t.is_ref then
          match t.data with
          | Int | Float | Bool | LongInt -> self#write_instruction0 REFREF
          | String | Array _ | Struct _ -> self#write_instruction0 REF
          | _ -> ()
        else
          match t.data with
          | String | Array _ | Struct _ | Delegate _ ->
              self#write_instruction0 REF
          | _ -> ()
      in
      match e.node with
      | Ident (_, LocalVariable i) -> (
          match self#get_local i with
          | { value_type = { data = String | Array _ | Struct _; _ }; _ } ->
              self#write_instruction1 SH_LOCALREF i
          | v ->
              self#compile_local_ref v.index;
              compile_lvalue_after v.value_type)
      | Ident (_, GlobalVariable i) -> (
          match Ain.get_global_by_index ain i with
          | { value_type = { data = String | Array _ | Struct _; _ }; _ } ->
              self#write_instruction1 SH_GLOBALREF i
          | v ->
              self#compile_global_ref v.index;
              compile_lvalue_after v.value_type)
      | Member (obj, _, ClassVariable (_, member_no)) -> (
          match (obj.node, e.ty) with
          | ( This,
              ( Ref (String | Array _ | Struct _)
              | String | Array _ | Struct _ | Delegate _ ) ) ->
              self#write_instruction1 SH_STRUCTREF member_no
          | _ ->
              self#compile_lvalue obj;
              self#write_instruction1 PUSH member_no;
              compile_lvalue_after (jaf_to_ain_type e.ty))
      | Subscript (obj, index) ->
          self#compile_lvalue obj;
          self#compile_expression index;
          compile_lvalue_after (jaf_to_ain_type e.ty)
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression e))
      | DummyRef (var_no, ref_expr) -> (
          self#scope_add_var (self#get_local var_no);
          (* prepare for assign to dummy variable *)
          self#write_instruction0 PUSHLOCALPAGE;
          self#write_instruction1 PUSH var_no;
          match ref_expr with
          | { node = New { ty = Struct (_, s_no); _ }; _ } ->
              self#write_instruction1 PUSH s_no;
              self#compile_lock_peek;
              self#write_instruction0 NEW;
              (* assign to dummy variable *)
              self#write_instruction0 ASSIGN;
              self#compile_unlock_peek
          | _ ->
              self#compile_expression ref_expr;
              self#write_instruction0
                (if is_ref_scalar ref_expr.ty then R_ASSIGN else ASSIGN))
      | This -> self#compile_expression e
      | Null -> (
          match e.ty with
          | Ref t ->
              self#write_instruction1 PUSH (-1);
              if is_numeric t then self#write_instruction1 PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL lvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression e)))
      | _ ->
          compiler_bug
            ("invalid lvalue: " ^ expr_to_string e)
            (Some (ASTExpression e))

    (** Emit the code to pop a value off the stack. *)
    method compile_pop (t : jaf_type) parent =
      match t with
      | Void -> ()
      | Int | Float | Bool | LongInt | FuncType _ | Ref _ ->
          self#write_instruction0 POP
      | String -> self#write_instruction0 S_POP
      | Delegate _ -> self#write_instruction0 DG_POP
      | Struct _ -> self#write_instruction0 SR_POP
      | IMainSystem | HLLParam | Array _ | Wrap _ | HLLFunc | TyFunction _
      | TyMethod _ | NullType | Untyped | Unresolved _ | Callback _ ->
          compiler_bug
            ("compile_pop: unsupported value type " ^ jaf_type_to_string t)
            (Some parent)

    method compile_argument (expr : expression option) (t : Ain.Type.t) =
      match expr with
      | None -> compiler_bug "missing argument" None
      | Some expr -> (
          match t with
          | { data = Method _; _ } ->
              (* XXX: for delegate builtins *)
              self#compile_expression expr
          | { data = _; is_ref = true } -> self#compile_lvalue expr
          | { data = Delegate _; _ } ->
              self#compile_expression expr;
              self#write_instruction0 DG_NEW_FROM_METHOD
          | _ -> self#compile_expression expr)

    method compile_function_arguments args (f : Ain.Function.t) =
      let compile_arg arg (var : Ain.Variable.t) =
        self#compile_argument arg var.value_type
      in
      List.iter2_exn args (Ain.Function.logical_parameters f) ~f:compile_arg

    (** Emit the code to call a method. The object upon which the method is to be
      called should already be on the stack before this code is executed. *)
    method compile_method_call args method_no =
      let f = Ain.get_function_by_index ain method_no in
      self#compile_function_arguments args f;
      self#write_instruction1 CALLMETHOD method_no

    (** Emit the code to compute an expression. Computing an expression produces
      a value (of the expression's value type) on the stack. *)
    method compile_expression (expr : expression) =
      match expr.node with
      | ConstInt i -> self#write_instruction1 PUSH i
      | ConstFloat f -> self#write_instruction1_float F_PUSH f
      | ConstChar s -> (
          Stdlib.Uchar.(
            let dec = Stdlib.String.get_utf_8_uchar s 0 in
            if
              not
                (utf_decode_is_valid dec
                && String.length s = utf_decode_length dec)
            then compile_error "Invalid character constant" (ASTExpression expr);
            match Sjis.from_uchar (utf_decode_uchar dec) with
            | Some c -> self#write_instruction1 PUSH c
            | None ->
                compile_error "Invalid character constant" (ASTExpression expr))
          )
      | ConstString s ->
          let no = Ain.add_string ain s in
          self#write_instruction1 S_PUSH no
      | Ident (_, LocalVariable i) -> (
          match (self#get_local i).value_type with
          | { data = Int | Float | Bool | LongInt | FuncType _; is_ref = false }
            ->
              self#write_instruction1 SH_LOCALREF i
          | t ->
              self#write_instruction0 PUSHLOCALPAGE;
              self#write_instruction1 PUSH i;
              self#compile_dereference t)
      | Ident (_, GlobalVariable i) -> (
          match (Ain.get_global_by_index ain i).value_type with
          | { data = Int | Float | Bool | LongInt | FuncType _; is_ref = false }
            ->
              self#write_instruction1 SH_GLOBALREF i
          | t ->
              self#write_instruction0 PUSHGLOBALPAGE;
              self#write_instruction1 PUSH i;
              self#compile_dereference t)
      | Ident (_, GlobalConstant) ->
          compiler_bug "global constant not eliminated"
            (Some (ASTExpression expr))
      | Ident (_, FunctionName _) ->
          compiler_bug "tried to compile function identifier"
            (Some (ASTExpression expr))
      | Ident (_, HLLName) ->
          compiler_bug "tried to compile HLL identifier"
            (Some (ASTExpression expr))
      | Ident (_, System) ->
          compiler_bug "tried to compile system identifier"
            (Some (ASTExpression expr))
      | Ident (_, BuiltinFunction _) ->
          compiler_bug "tried to compile built-in function identifier"
            (Some (ASTExpression expr))
      | Ident (_, UnresolvedIdent) ->
          compiler_bug "identifier type is none" (Some (ASTExpression expr))
      | Unary (UPlus, e) -> self#compile_expression e
      | Unary (UMinus, e) ->
          self#compile_expression e;
          self#write_instruction0 INV
      | Unary (LogNot, e) ->
          self#compile_expression e;
          self#write_instruction0 NOT
      | Unary (BitNot, e) ->
          self#compile_expression e;
          self#write_instruction0 COMPL
      | Unary (AddrOf, e) -> (
          match (e.ty, e.node) with
          | TyFunction (_, no), _ -> self#write_instruction1 PUSH no
          | TyMethod (_, no), Member (e, _, ClassMethod _) ->
              self#compile_lvalue e;
              self#write_instruction1 PUSH no
          | _ ->
              compiler_bug "invalid type for & operator"
                (Some (ASTExpression expr)))
      | Unary (PreInc, e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 INC;
          self#write_instruction0 REF
      | Unary (PreDec, e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 DEC;
          self#write_instruction0 REF
      | Unary (PostInc, e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DUP_X2;
          self#write_instruction0 POP;
          self#write_instruction0 INC
      | Unary (PostDec, e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 REF;
          self#write_instruction0 DUP_X2;
          self#write_instruction0 POP;
          self#write_instruction0 DEC
      | Binary (LogOr, a, b) ->
          self#compile_expression a;
          let lhs_true_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          self#compile_expression b;
          let rhs_true_addr = current_address + 2 in
          self#write_instruction1 IFNZ 0;
          self#write_instruction1 PUSH 0;
          let false_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at lhs_true_addr current_address;
          self#write_address_at rhs_true_addr current_address;
          self#write_instruction1 PUSH 1;
          self#write_address_at false_addr current_address
      | Binary (LogAnd, a, b) ->
          self#compile_expression a;
          let lhs_false_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_expression b;
          let rhs_false_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#write_instruction1 PUSH 1;
          let true_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at lhs_false_addr current_address;
          self#write_address_at rhs_false_addr current_address;
          self#write_instruction1 PUSH 0;
          self#write_address_at true_addr current_address
      | Binary (op, a, b) -> (
          (match op with
          | RefEqual | RefNEqual ->
              self#compile_lvalue a;
              self#compile_lvalue b
          | _ ->
              self#compile_expression a;
              self#compile_expression b);
          match (a.ty, op) with
          | (Int | LongInt | Bool), Equal -> self#write_instruction0 EQUALE
          | (Int | LongInt | Bool), NEqual -> self#write_instruction0 NOTE
          | Int, Plus -> self#write_instruction0 ADD
          | Int, Minus -> self#write_instruction0 SUB
          | Int, Times -> self#write_instruction0 MUL
          | Int, Divide -> self#write_instruction0 DIV
          | Int, Modulo -> self#write_instruction0 MOD
          | (Int | LongInt), LT -> self#write_instruction0 LT
          | (Int | LongInt), GT -> self#write_instruction0 GT
          | (Int | LongInt), LTE -> self#write_instruction0 LTE
          | (Int | LongInt), GTE -> self#write_instruction0 GTE
          | Int, BitOr -> self#write_instruction0 OR
          | Int, BitXor -> self#write_instruction0 XOR
          | Int, BitAnd -> self#write_instruction0 AND
          | Int, LShift -> self#write_instruction0 LSHIFT
          | Int, RShift -> self#write_instruction0 RSHIFT
          | Int, (LogOr | LogAnd) ->
              compiler_bug "invalid integer operator"
                (Some (ASTExpression expr))
          | LongInt, Plus -> self#write_instruction0 LI_ADD
          | LongInt, Minus -> self#write_instruction0 LI_SUB
          | LongInt, Times -> self#write_instruction0 LI_MUL
          | LongInt, Divide -> self#write_instruction0 LI_DIV
          | LongInt, Modulo -> self#write_instruction0 LI_MOD
          | Float, Plus -> self#write_instruction0 F_ADD
          | Float, Minus -> self#write_instruction0 F_SUB
          | Float, Times -> self#write_instruction0 F_MUL
          | Float, Divide -> self#write_instruction0 F_DIV
          | Float, Equal -> self#write_instruction0 F_EQUALE
          | Float, NEqual -> self#write_instruction0 F_NOTE
          | Float, LT -> self#write_instruction0 F_LT
          | Float, GT -> self#write_instruction0 F_GT
          | Float, LTE -> self#write_instruction0 F_LTE
          | Float, GTE -> self#write_instruction0 F_GTE
          | ( Float,
              ( Modulo | BitOr | BitXor | BitAnd | LShift | RShift | LogOr
              | LogAnd ) ) ->
              compiler_bug "invalid floating point operator"
                (Some (ASTExpression expr))
          | String, Plus -> self#write_instruction0 S_ADD
          | String, Equal -> self#write_instruction0 S_EQUALE
          | String, NEqual -> self#write_instruction0 S_NOTE
          | String, LT -> self#write_instruction0 S_LT
          | String, GT -> self#write_instruction0 S_GT
          | String, LTE -> self#write_instruction0 S_LTE
          | String, GTE -> self#write_instruction0 S_GTE
          | String, Modulo ->
              let int_of_t (t : Ain.Type.data) =
                match t with
                | Int -> 2
                | Float -> 3
                | String -> 4
                | Bool -> 48
                | _ ->
                    compiler_bug "invalid type for string formatting"
                      (Some (ASTExpression expr))
              in
              self#write_instruction1 S_MOD
                (int_of_t (jaf_to_ain_type b.ty).data)
          | ( String,
              ( Minus | Times | Divide | BitOr | BitXor | BitAnd | LShift
              | RShift | LogOr | LogAnd ) ) ->
              compiler_bug "invalid string operator" (Some (ASTExpression expr))
          | Ref t, RefEqual ->
              self#write_instruction0
                (if is_numeric t then R_EQUALE else EQUALE)
          | Ref t, RefNEqual ->
              self#write_instruction0 (if is_numeric t then R_NOTE else NOTE)
          | FuncType _, Equal -> self#write_instruction0 EQUALE
          | FuncType _, NEqual -> self#write_instruction0 NOTE
          | _ ->
              compiler_bug "invalid binary expression"
                (Some (ASTExpression expr)))
      | Assign (op, lhs, rhs) -> (
          self#compile_lvalue lhs;
          self#compile_expression rhs;
          match (op, rhs.ty) with
          | EqAssign, (Int | Bool | Ref (TyFunction _) | FuncType _) ->
              self#write_instruction0 ASSIGN
          | PlusAssign, (Int | Bool) -> self#write_instruction0 PLUSA
          | MinusAssign, (Int | Bool) -> self#write_instruction0 MINUSA
          | TimesAssign, (Int | Bool) -> self#write_instruction0 MULA
          | DivideAssign, (Int | Bool) -> self#write_instruction0 DIVA
          | ModuloAssign, (Int | Bool) -> self#write_instruction0 MODA
          | OrAssign, (Int | Bool) -> self#write_instruction0 ORA
          | XorAssign, (Int | Bool) -> self#write_instruction0 XORA
          | AndAssign, (Int | Bool) -> self#write_instruction0 ANDA
          | LShiftAssign, (Int | Bool) -> self#write_instruction0 LSHIFTA
          | RShiftAssign, (Int | Bool) -> self#write_instruction0 RSHIFTA
          | CharAssign, Int -> self#write_instruction0 C_ASSIGN
          | EqAssign, LongInt -> self#write_instruction0 LI_ASSIGN
          | PlusAssign, LongInt -> self#write_instruction0 LI_PLUSA
          | MinusAssign, LongInt -> self#write_instruction0 LI_MINUSA
          | TimesAssign, LongInt -> self#write_instruction0 LI_MULA
          | DivideAssign, LongInt -> self#write_instruction0 LI_DIVA
          | ModuloAssign, LongInt -> self#write_instruction0 LI_MODA
          | AndAssign, LongInt -> self#write_instruction0 LI_ANDA
          | OrAssign, LongInt -> self#write_instruction0 LI_ORA
          | XorAssign, LongInt -> self#write_instruction0 LI_XORA
          | LShiftAssign, LongInt -> self#write_instruction0 LI_LSHIFTA
          | RShiftAssign, LongInt -> self#write_instruction0 LI_RSHIFTA
          | EqAssign, Float -> self#write_instruction0 F_ASSIGN
          | PlusAssign, Float -> self#write_instruction0 F_PLUSA
          | MinusAssign, Float -> self#write_instruction0 F_MINUSA
          | TimesAssign, Float -> self#write_instruction0 F_MULA
          | DivideAssign, Float -> self#write_instruction0 F_DIVA
          | EqAssign, String -> (
              match lhs.ty with
              | FuncType (_, ft_i) ->
                  self#write_instruction1 PUSH ft_i;
                  self#write_instruction0 FT_ASSIGNS
              | String -> self#write_instruction0 S_ASSIGN
              | _ ->
                  compiler_bug "invalid string assignment"
                    (Some (ASTExpression expr)))
          | PlusAssign, String -> self#write_instruction0 S_PLUSA2
          | EqAssign, Ref (TyMethod _) ->
              (* XXX: DG_SET and DG_ADD seem to be misnamed... *)
              self#write_instruction0 DG_ADD
          | EqAssign, Delegate _ -> self#write_instruction0 DG_ASSIGN
          | PlusAssign, Ref (TyMethod _) -> self#write_instruction0 DG_SET
          | PlusAssign, Delegate _ -> self#write_instruction0 DG_PLUSA
          | MinusAssign, Ref (TyMethod _) -> self#write_instruction0 DG_ERASE
          | MinusAssign, Delegate _ -> self#write_instruction0 DG_MINUSA
          | EqAssign, Struct (_, sno) ->
              self#write_instruction1 PUSH sno;
              self#write_instruction0 SR_ASSIGN
          | _, _ ->
              compiler_bug "invalid assignment" (Some (ASTExpression expr)))
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expression b
      | Ternary (test, con, alt) ->
          self#compile_expression test;
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_expression con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_expression alt;
          self#write_address_at jump_addr current_address
      | Cast (_, e) -> (
          let dst_t = expr.ty in
          let src_t = e.ty in
          self#compile_expression e;
          match (src_t, dst_t) with
          | Int, Int -> ()
          | Int, Bool -> self#write_instruction0 ITOB
          | Int, Float -> self#write_instruction0 ITOF
          | Int, LongInt -> self#write_instruction0 ITOLI
          | Int, String -> self#write_instruction0 I_STRING
          | Bool, (Bool | Int) -> ()
          | Float, Float -> ()
          | Float, Int -> self#write_instruction0 FTOI
          | Float, String ->
              self#write_instruction1 PUSH 6;
              self#write_instruction0 FTOS
          | String, String -> ()
          | String, Int -> self#write_instruction0 STOI
          | _ -> compiler_bug "invalid cast" (Some (ASTExpression expr)))
      | Subscript (obj, index) -> (
          self#compile_lvalue obj;
          self#compile_expression index;
          match obj.ty with
          | String -> self#write_instruction0 C_REF
          | _ -> self#compile_dereference (jaf_to_ain_type expr.ty))
      | Member ({ node = This; _ }, _, ClassVariable (_, member_no))
        when is_scalar expr.ty ->
          self#write_instruction1 SH_STRUCTREF member_no
      | Member (e, _, ClassVariable (struct_no, member_no)) ->
          let struct_type = Ain.get_struct_by_index ain struct_no in
          self#compile_lvalue e;
          self#write_instruction1 PUSH member_no;
          self#compile_dereference
            (List.nth_exn struct_type.members member_no).value_type
      | Member (_, _, ClassConst _) ->
          compiler_bug "class constant not eliminated"
            (Some (ASTExpression expr))
      | Member (_, _, ClassMethod _) ->
          compiler_bug "tried to compile method member expression"
            (Some (ASTExpression expr))
      | Member (_, _, HLLFunction (_, _)) ->
          compiler_bug "tried to compile HLL member expression"
            (Some (ASTExpression expr))
      | Member (_, _, SystemFunction _) ->
          compiler_bug "tried to compile system call member expression"
            (Some (ASTExpression expr))
      | Member (_, _, BuiltinMethod _) ->
          compiler_bug "tried to compile built-in method member expression"
            (Some (ASTExpression expr))
      | Member (_, _, UnresolvedMember) ->
          compiler_bug "member expression has no member_type"
            (Some (ASTExpression expr))
      (* regular function call *)
      | Call (_, args, FunctionCall function_no) ->
          let f = Ain.get_function_by_index ain function_no in
          self#compile_function_arguments args f;
          self#write_instruction1 CALLFUNC function_no
      (* method call *)
      | Call ({ node = Member (e, _, _); _ }, args, MethodCall (_, method_no))
        ->
          self#compile_lvalue e;
          self#compile_method_call args method_no
      (* HLL function call *)
      | Call (_, args, HLLCall (lib_no, fun_no)) ->
          let f = Ain.function_of_hll_function_index ain lib_no fun_no in
          self#compile_function_arguments args f;
          self#write_instruction2 CALLHLL lib_no fun_no
      (* system call *)
      | Call (_, args, SystemCall sys) ->
          let f = Builtin.function_of_syscall sys in
          self#compile_function_arguments args f;
          self#write_instruction1 CALLSYS f.index
      (* built-in method call *)
      | Call ({ node = Member (e, _, _); _ }, args, BuiltinCall builtin) -> (
          let receiver_ty = ref Void in
          (match builtin with
          | (StringLength | StringLengthByte) when is_variable_ref e.node ->
              self#compile_variable_ref e
          | IntString | FloatString | StringInt | StringLength
          | StringLengthByte | StringEmpty | StringFind | StringGetPart ->
              self#compile_expression e
          | StringPushBack | StringPopBack | StringErase | DelegateSet
          | DelegateAdd | DelegateNumof | DelegateExist | DelegateErase
          | DelegateClear ->
              self#compile_lvalue e
          | ArrayAlloc | ArrayRealloc | ArrayFree | ArrayNumof | ArrayCopy
          | ArrayFill | ArrayPushBack | ArrayPopBack | ArrayEmpty | ArrayErase
          | ArrayInsert | ArraySort | ArrayReverse | ArrayFind ->
              receiver_ty := e.ty;
              self#compile_variable_ref e
          | Assert ->
              compiler_bug "invalid assert expression"
                (Some (ASTExpression expr)));
          let f = Builtin.function_of_builtin builtin !receiver_ty in
          self#compile_function_arguments args f;
          match builtin with
          | IntString -> self#write_instruction0 I_STRING
          | FloatString ->
              self#write_instruction1 PUSH 6;
              self#write_instruction0 ITOF
          | StringInt -> self#write_instruction0 STOI
          | StringLength ->
              self#write_instruction0
                (if is_variable_ref e.node then S_LENGTH else S_LENGTH2)
          | StringLengthByte ->
              self#write_instruction0
                (if is_variable_ref e.node then S_LENGTHBYTE else S_LENGTHBYTE2)
          | StringEmpty -> self#write_instruction0 S_EMPTY
          | StringFind -> self#write_instruction0 S_FIND
          | StringGetPart -> self#write_instruction0 S_GETPART
          | StringPushBack -> self#write_instruction0 S_PUSHBACK2
          | StringPopBack -> self#write_instruction0 S_POPBACK2
          | StringErase -> self#write_instruction0 S_ERASE2
          | ArrayAlloc ->
              self#write_instruction1 PUSH (List.length args);
              self#write_instruction0 A_ALLOC
          | ArrayRealloc ->
              (* FIXME: this built-in should be variadic *)
              self#write_instruction1 PUSH 1;
              self#write_instruction0 A_REALLOC
          | ArrayFree -> self#write_instruction0 A_FREE
          | ArrayNumof -> self#write_instruction0 A_NUMOF
          | ArrayCopy -> self#write_instruction0 A_COPY
          | ArrayFill -> self#write_instruction0 A_FILL
          | ArrayPushBack -> self#write_instruction0 A_PUSHBACK
          | ArrayPopBack -> self#write_instruction0 A_POPBACK
          | ArrayEmpty -> self#write_instruction0 A_EMPTY
          | ArrayErase -> self#write_instruction0 A_ERASE
          | ArrayInsert -> self#write_instruction0 A_INSERT
          | ArraySort -> self#write_instruction0 A_SORT
          | ArrayReverse -> self#write_instruction0 A_REVERSE
          | ArrayFind -> self#write_instruction0 A_FIND
          | DelegateSet -> self#write_instruction0 DG_SET
          | DelegateAdd -> self#write_instruction0 DG_ADD
          | DelegateNumof -> self#write_instruction0 DG_NUMOF
          | DelegateExist -> self#write_instruction0 DG_EXIST
          | DelegateErase -> self#write_instruction0 DG_ERASE
          | DelegateClear -> self#write_instruction0 DG_CLEAR
          | Assert ->
              compiler_bug "invalid built-in method call"
                (Some (ASTExpression expr)))
      (* built-in function call *)
      | Call ({ node = Ident _; _ }, args, BuiltinCall builtin) -> (
          let f = Builtin.function_of_builtin builtin Void in
          self#compile_function_arguments args f;
          match builtin with
          | Assert -> self#write_instruction0 ASSERT
          | _ ->
              compiler_bug "invalid built-in function call"
                (Some (ASTExpression expr)))
      (* functype call *)
      | Call (e, args, FuncTypeCall no) ->
          let compile_arg arg (var : Ain.Variable.t) =
            self#compile_argument arg var.value_type;
            if is_ref_scalar (ain_to_jaf_type var.value_type) then (
              self#write_instruction0 DUP2_X1;
              self#write_instruction0 POP;
              self#write_instruction0 POP)
            else self#write_instruction0 SWAP
          in
          let f = Ain.get_functype_by_index ain no in
          self#compile_expression e;
          List.iter2_exn args
            (Ain.FunctionType.logical_parameters f)
            ~f:compile_arg;
          self#write_instruction1 PUSH no;
          self#write_instruction0 CALLFUNC2
      | Call (e, args, DelegateCall no) ->
          let f = Ain.function_of_delegate_index ain no in
          self#compile_lvalue e;
          self#compile_function_arguments args f;
          self#write_instruction1 DG_CALLBEGIN no;
          let loop_addr = current_address in
          self#write_instruction2 DG_CALL no 0;
          self#write_instruction1 JUMP loop_addr;
          self#write_address_at (loop_addr + 6) current_address
      | Call (_, _, _) ->
          compiler_bug "invalid call expression" (Some (ASTExpression expr))
      | New _ -> compiler_bug "bare new expression" (Some (ASTExpression expr))
      | DummyRef _ -> self#compile_lvalue expr
      | This -> self#write_instruction0 PUSHSTRUCTPAGE
      | Null -> (
          match expr.ty with
          | FuncType _ | IMainSystem -> self#write_instruction1 PUSH 0
          | String -> self#write_instruction1 S_PUSH 0
          | ty ->
              compiler_bug
                ("unimplemented: NULL rvalue of type " ^ jaf_type_to_string ty)
                (Some (ASTExpression expr)))

    method compile_expr_and_pop (expr : expression) =
      match expr.node with
      | Assign
          ( EqAssign,
            { node = Ident (_, LocalVariable i); _ },
            { node = ConstInt n; _ } )
        when not (self#get_local i).value_type.is_ref ->
          self#write_instruction2 SH_LOCALASSIGN i n
      | Unary
          ( ((PreInc | PostInc | PreDec | PostDec) as op),
            { node = Ident (_, LocalVariable i); _ } )
        when not (self#get_local i).value_type.is_ref ->
          self#write_instruction1
            (match op with PreInc | PostInc -> SH_LOCALINC | _ -> SH_LOCALDEC)
            i
      | Unary (((PreInc | PreDec) as op), e) ->
          self#compile_lvalue e;
          self#write_instruction0 DUP2;
          self#write_instruction0 (match op with PreInc -> INC | _ -> DEC);
          self#write_instruction0 POP;
          self#write_instruction0 POP
      | Seq (a, b) ->
          self#compile_expr_and_pop a;
          self#compile_expr_and_pop b
      | _ ->
          self#compile_expression expr;
          self#compile_pop expr.ty (ASTExpression expr)

    (** Emit the code for a statement. Statements are stack-neutral, i.e. the
      state of the stack is unchanged after executing a statement. *)
    method compile_statement (stmt : statement) =
      (* delete locals that will be out-of-scope after this statement *)
      List.iter stmt.delete_vars ~f:(fun i ->
          self#compile_delete_var (self#get_local i));
      match stmt.node with
      | EmptyStatement -> ()
      | Declarations decls ->
          List.iter decls.vars ~f:self#compile_variable_declaration
      | Expression e -> self#compile_expr_and_pop e
      | Compound stmts -> self#compile_block stmts
      | Label name -> self#scope_add_label name
      | If (test, con, alt) ->
          self#compile_expression test;
          let ifz_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          self#compile_statement con;
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          self#write_address_at ifz_addr current_address;
          self#compile_statement alt;
          self#write_address_at jump_addr current_address
      | While (test, body) ->
          (* loop test *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          self#compile_expression test;
          let break_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          (* loop body *)
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          self#write_address_at break_addr current_address;
          self#end_loop
      | DoWhile (test, body) ->
          (* skip loop test *)
          let jump_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          (* loop test *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          self#compile_expression test;
          let break_addr = current_address + 2 in
          self#write_instruction1 IFZ 0;
          (* loop body *)
          self#write_address_at jump_addr current_address;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          self#write_address_at break_addr current_address;
          self#end_loop
      | For (decl, None, None, body) ->
          (* loop init *)
          self#compile_block [ decl ];
          (* loop body *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          self#end_loop
      | For (decl, test, inc, body) ->
          (* loop init *)
          self#compile_block [ decl ];
          (* loop test *)
          let test_addr = current_address in
          let break_addr =
            Option.map test ~f:(fun e ->
                self#compile_expression e;
                let break_addr = current_address + 2 in
                self#write_instruction1 IFZ 0;
                break_addr)
          in
          let body_addr = current_address + 2 in
          self#write_instruction1 JUMP 0;
          (* loop increment *)
          let loop_addr = current_address in
          self#start_loop loop_addr;
          (* self#set_continue_addr loop_addr; *)
          Option.iter inc ~f:self#compile_expr_and_pop;
          self#write_instruction1 JUMP test_addr;
          (* loop body *)
          self#write_address_at body_addr current_address;
          self#compile_statement body;
          self#write_instruction1 JUMP loop_addr;
          (* loop end *)
          Option.iter break_addr ~f:(fun break_addr ->
              self#write_address_at break_addr current_address);
          self#end_loop
      | Goto name ->
          self#scope_add_goto name (current_address + 2) stmt;
          self#write_instruction1 JUMP 0
      | Continue ->
          self#write_instruction1 JUMP
            (self#get_continue_addr (ASTStatement stmt))
      | Break ->
          self#push_break_addr (current_address + 2) (ASTStatement stmt);
          self#write_instruction1 JUMP 0
      | Switch (expr, stmts) ->
          self#compile_expression expr;
          self#write_instruction1 SWITCH self#start_switch;
          self#push_break_addr (current_address + 2) (ASTStatement stmt);
          self#write_instruction1 JUMP 0;
          List.iter stmts ~f:self#compile_statement;
          self#end_switch
      | Case { node = ConstInt i; _ } ->
          self#add_switch_case i (ASTStatement stmt)
      | Case _ ->
          compile_error "invalid expression in switch case" (ASTStatement stmt)
      | Default -> self#set_switch_default (ASTStatement stmt)
      | Return None -> self#write_instruction0 RETURN
      | Return (Some e) ->
          (match (Option.value_exn current_function).return_type with
          | { is_ref = true; data = Int | Float | Bool | LongInt | FuncType _ }
            ->
              self#compile_lvalue e;
              self#write_instruction0 DUP_U2;
              self#write_instruction0 SP_INC
          | { is_ref = true; data = String | Struct _ | Array _ } ->
              self#compile_lvalue e;
              self#write_instruction0 DUP;
              self#write_instruction0 SP_INC
          | { is_ref = true; _ } ->
              compile_error "return statement not implemented for ref type"
                (ASTStatement stmt)
          | _ -> self#compile_expression e);
          self#write_instruction0 RETURN
      | Jump funcname ->
          let no = Ain.add_string ain funcname in
          self#write_instruction1 S_PUSH no;
          self#write_instruction0 CALLONJUMP;
          self#write_instruction0 SJUMP
      | Jumps e ->
          self#compile_expression e;
          self#write_instruction0 CALLONJUMP;
          self#write_instruction0 SJUMP
      | Message msg ->
          let msg_no = Ain.add_message ain msg in
          self#write_instruction1 MSG msg_no
      | RefAssign (lhs, rhs) ->
          self#compile_lock_peek;
          self#compile_variable_ref lhs;
          self#compile_delete_ref lhs.ty;
          (match (lhs.ty, rhs.node) with
          | _, Null -> ()
          | _ -> self#write_instruction0 DUP2);
          self#compile_lvalue rhs;
          (match lhs.ty with
          | _ when is_ref_scalar lhs.ty -> (
              (* NOTE: SDK compiler emits [DUP_U2; SP_INC; R_ASSIGN; POP; POP] here *)
              self#write_instruction0 R_ASSIGN;
              self#write_instruction0 POP;
              match rhs.node with
              | Null -> self#write_instruction0 POP
              | _ ->
                  self#write_instruction0 POP;
                  self#write_instruction0 REF;
                  self#write_instruction0 SP_INC)
          | Ref (String | Struct _ | Array _) -> (
              (* NOTE: SDK compiler emits [DUP; SP_INC; ASSIGN; POP] here *)
              self#write_instruction0 ASSIGN;
              match rhs.node with
              | Null -> self#write_instruction0 POP
              | _ ->
                  self#write_instruction0 DUP_X2;
                  self#write_instruction0 POP;
                  self#write_instruction0 REF;
                  self#write_instruction0 SP_INC;
                  self#write_instruction0 POP)
          | _ ->
              compiler_bug "Invalid LHS in reference assignment"
                (Some (ASTStatement stmt)));
          self#compile_unlock_peek
      | ObjSwap (a, b) ->
          (* FIXME: this doesn't work for string / struct *)
          self#compile_lvalue a;
          self#compile_lvalue b;
          let type_no =
            Ain.Type.int_of_data_type (Ain.version ain) (jaf_to_ain_type a.ty)
          in
          self#write_instruction1 PUSH type_no;
          self#write_instruction0 OBJSWAP

    (** Emit the code for a variable declaration. If the variable has an initval,
      the initval expression is computed and assigned to the variable.
      Otherwise a default value is assigned. *)
    method compile_variable_declaration (decl : variable) =
      if decl.is_const then ()
      else
        let v = self#get_local (Option.value_exn decl.index) in
        self#scope_add_var v;
        if v.value_type.is_ref then
          let lhs =
            {
              node = Ident (decl.name, LocalVariable v.index);
              ty = decl.type_spec.ty;
              loc = decl.location;
            }
          and rhs =
            match decl.initval with
            | Some e -> e
            | None -> make_expr ~ty:decl.type_spec.ty Null
          in
          self#compile_statement
            {
              node = RefAssign (lhs, rhs);
              delete_vars = [];
              loc = decl.location;
            }
        else
          match v.value_type.data with
          | Int | Bool | LongInt | Float | FuncType _ | String ->
              let lhs =
                {
                  node = Ident (decl.name, LocalVariable v.index);
                  ty = decl.type_spec.ty;
                  loc = decl.location;
                }
              in
              let rhs =
                match decl.initval with
                | Some e -> e
                | None ->
                    let value =
                      match v.value_type.data with
                      | Int | Bool | LongInt -> ConstInt 0
                      | Float -> ConstFloat 0.0
                      | FuncType _ | String -> Null
                      | _ -> failwith "unreachable"
                    in
                    make_expr ~ty:decl.type_spec.ty value
              in
              self#compile_expr_and_pop
                {
                  node = Assign (EqAssign, lhs, rhs);
                  ty = decl.type_spec.ty;
                  loc = decl.location;
                }
          | Struct sno -> (
              (* FIXME: use verbose versions *)
              self#write_instruction1 SH_LOCALDELETE v.index;
              self#write_instruction2 SH_LOCALCREATE v.index sno;
              match decl.initval with
              | Some e ->
                  self#compile_lvalue
                    {
                      node = Ident (decl.name, LocalVariable v.index);
                      ty = decl.type_spec.ty;
                      loc = decl.location;
                    };
                  self#compile_expression e;
                  self#write_instruction1 PUSH sno;
                  self#write_instruction0 SR_ASSIGN;
                  self#compile_pop decl.type_spec.ty (ASTVariable decl)
              | None -> ())
          | Array _ ->
              let has_dims = List.length decl.array_dim > 0 in
              self#compile_local_ref v.index;
              if has_dims then (
                List.iter decl.array_dim ~f:self#compile_expression;
                self#write_instruction1 PUSH (List.length decl.array_dim);
                self#write_instruction0 A_ALLOC)
              else self#write_instruction0 A_FREE
          | Delegate _ -> (
              self#compile_local_ref v.index;
              self#write_instruction0 REF;
              match decl.initval with
              | Some e ->
                  self#compile_expression e;
                  self#write_instruction0 DG_SET
              | None -> self#write_instruction0 DG_CLEAR)
          | Void | IMainSystem | HLLFunc2 | HLLParam | Wrap _ | Option _
          | Unknown87 _ | IFace _ | Enum2 _ | Enum _ | HLLFunc | Unknown98
          | IFaceWrap _ | Function _ | Method _ | NullType ->
              compile_error "Unimplemented variable type" (ASTVariable decl)

    (** Emit the code for a block of statements. *)
    method compile_block (stmts : statement list) =
      self#start_scope;
      List.iter stmts ~f:self#compile_statement;
      self#end_scope

    (** Emit the code for a default return value. *)
    method compile_default_return (t : Ain.Type.t) decl =
      if t.is_ref then
        match t.data with
        | String | Struct _ | Array _ -> self#write_instruction1 PUSH (-1)
        | Int | Float | Bool | LongInt ->
            self#write_instruction1 PUSH (-1);
            self#write_instruction1 PUSH 0
        | _ ->
            compile_error "default return value not implemented for ref type"
              decl
      else
        match t.data with
        | Void -> ()
        | Int | Bool | LongInt -> self#write_instruction1 PUSH 0
        | Float -> self#write_instruction1 F_PUSH 0
        | String -> self#write_instruction1 S_PUSH 0
        | Struct _ | Array _ -> self#write_instruction1 PUSH (-1)
        | _ ->
            compile_error "default return value not implemented for type" decl

    (** Emit the code for a function. *)
    method compile_function (decl : fundecl) =
      let index = Option.value_exn decl.index in
      let func =
        {
          (Ain.get_function_by_index ain index) with
          address = current_address + 6;
        }
      in
      current_function <- Some func;
      self#write_instruction1 FUNC index;
      self#compile_block (Option.value_exn decl.body);
      if not func.is_label then (
        self#compile_default_return func.return_type
          (ASTDeclaration (Function decl));
        self#write_instruction0 RETURN);
      (* ENDFUNC is not generated for the "NULL" function and methods except
         auto-generated array initializers. *)
      (match decl with
      | { name = "NULL"; _ } -> ()
      | { class_name = None; _ } | { name = "2"; _ } ->
          self#write_instruction1 ENDFUNC index
      | _ -> ());
      Ain.write_function ain func;
      current_function <- None

    (** Compile a list of declarations. *)
    method compile jaf_name (decls : declaration list) =
      start_address <- Ain.code_size ain;
      current_address <- start_address;
      let compile_decl = function
        | Jaf.Function f -> self#compile_function f
        | Global _ | GlobalGroup _ | FuncTypeDef _ | DelegateDef _ -> ()
        | StructDef d ->
            let compile_struct_decl (d : struct_declaration) =
              match d with
              | AccessSpecifier _ -> ()
              | MemberDecl _ -> () (* TODO: member initvals? *)
              | Constructor f | Destructor f | Method f ->
                  if Option.is_some f.body then self#compile_function f
            in
            List.iter d.decls ~f:compile_struct_decl
        | Enum e ->
            (* TODO: built-in enum methods *)
            compile_error "Enums not implemented" (ASTDeclaration (Enum e))
      in
      List.iter decls ~f:compile_decl;
      let jaf_name = String.tr ~target:'/' ~replacement:'\\' jaf_name in
      self#write_instruction1 EOF (Ain.add_file ain jaf_name);
      self#write_buffer
  end

let compile ctx jaf_name decls =
  (new jaf_compiler ctx.ain)#compile jaf_name decls
