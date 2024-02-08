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

type scope_kind = ScopeAnon | ScopeLoop | ScopeSwitch
type var_set = (int, Int.comparator_witness) Set.t

type scope = {
  (* variables allocated before entering the scope *)
  initial_vars : var_set;
  (* list of labels, including the list of variables allocated at each label *)
  (* when leaving a scope, this list is NOT inherited by the parent scope *)
  mutable labels : (string * var_set) list;
  (* list of unresolved goto statements *)
  (* when leaving a scope, this list is inherited by the parent scope *)
  mutable gotos : (statement * var_set) list;
  (* list of unresolved break statements *)
  mutable breaks : (statement * var_set) list;
  (* list of unresolved continue statements *)
  mutable continues : (statement * var_set) list;
}

class variable_alloc_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable vars : variable list = []
    val scopes = Stack.create ()

    method start_scope =
      let initial_vars = Set.of_list (module Int) environment#var_id_list in
      Stack.push scopes
        { initial_vars; labels = []; gotos = []; breaks = []; continues = [] }

    method end_scope kind =
      let scope = Stack.pop_exn scopes in
      (* resolve gotos *)
      let rec update_gotos gotos unresolved =
        match gotos with
        | (({ node = Goto name; _ } as goto), goto_vars) :: rest -> (
            match
              List.find scope.labels ~f:(fun (label_name, _) ->
                  String.equal name label_name)
            with
            | Some (_, label_vars) ->
                (* variables which aren't in-scope at the target label should be deleted *)
                goto.delete_vars <- Set.elements (Set.diff goto_vars label_vars);
                update_gotos rest unresolved
            | None -> update_gotos rest ((goto, goto_vars) :: unresolved))
        | (stmt, _) :: _ ->
            compiler_bug "Invalid statement in goto list"
              (Some (ASTStatement stmt))
        | [] -> unresolved
      in
      let unresolved = update_gotos scope.gotos [] in
      (* unresolved gotos are moved to the parent scope *)
      (match (Stack.top scopes, unresolved) with
      | _, [] -> ()
      | None, (stmt, _) :: _ ->
          compile_error "Unresolved label" (ASTStatement stmt)
      | Some parent, unresolved ->
          parent.gotos <- List.append parent.gotos unresolved);
      let update_break_continue (stmt, vars) =
        stmt.delete_vars <- Set.elements (Set.diff vars scope.initial_vars)
      in
      (* function to transfer breaks to parent scope *)
      let carry_breaks () =
        match Stack.top scopes with
        | None -> (
            match scope.breaks with
            | [] -> ()
            | (stmt, _) :: _ ->
                compile_error "Unresolved break statement" (ASTStatement stmt))
        | Some parent -> parent.breaks <- List.append parent.breaks scope.breaks
      in
      (* function to transfer continues to parent scope *)
      let carry_continues () =
        match Stack.top scopes with
        | None -> (
            match scope.continues with
            | [] -> ()
            | (stmt, _) :: _ ->
                compile_error "Unresolved continue statement"
                  (ASTStatement stmt))
        | Some parent ->
            parent.continues <- List.append parent.continues scope.continues
      in
      match kind with
      | ScopeLoop ->
          List.iter scope.breaks ~f:update_break_continue;
          List.iter scope.continues ~f:update_break_continue
      | ScopeSwitch ->
          List.iter scope.breaks ~f:update_break_continue;
          carry_continues ()
      | ScopeAnon ->
          carry_breaks ();
          carry_continues ()

    method current_var_set = Set.of_list (module Int) environment#var_id_list

    method add_continue stmt =
      let scope = Stack.top_exn scopes in
      scope.continues <- (stmt, self#current_var_set) :: scope.continues

    method add_break stmt =
      let scope = Stack.top_exn scopes in
      scope.breaks <- (stmt, self#current_var_set) :: scope.breaks

    method add_label name =
      let scope = Stack.top_exn scopes in
      scope.labels <- (name, self#current_var_set) :: scope.labels

    method add_goto stmt =
      let scope = Stack.top_exn scopes in
      scope.gotos <- (stmt, self#current_var_set) :: scope.gotos

    method get_var_no name =
      let rec search i (vars : variable list) =
        match vars with
        | hd :: tl -> if String.equal hd.name name then i else search (i + 1) tl
        | [] -> compiler_bug ("Undefined variable: " ^ name) None
      in
      search 0 (List.rev vars)

    method add_var (v : variable) =
      let i = List.length vars in
      v.index <- Some i;
      match v.type_spec with
      | { data = Int | Bool | Float | FuncType (_, _); qualifier = Some Ref } ->
          let void =
            {
              name = "<void>";
              location = v.location;
              array_dim = [];
              type_spec = { data = Void; qualifier = None };
              initval = None;
              index = Some (i + 1);
            }
          in
          vars <- void :: v :: vars
      | _ -> vars <- v :: vars

    method! visit_expression expr =
      super#visit_expression expr;
      match expr.node with
      | Ident (name, t) -> (
          (* save local variable number at identifier nodes *)
          match t with
          | Some (LocalVariable _) ->
              expr.node <-
                Ident (name, Some (LocalVariable (self#get_var_no name)))
          | _ -> ())
      | New (t, args, _) ->
          (* create dummy ref variable to store object for extent of new expression *)
          let struct_name =
            match t with
            | Struct (name, _) -> name
            | _ ->
                compiler_bug "Non-struct type in new expression"
                  (Some (ASTExpression expr))
          in
          let v =
            {
              name = "<dummy : new " ^ struct_name ^ ">";
              location = expr.loc;
              array_dim = [];
              type_spec = { data = t; qualifier = Some Ref };
              initval = None;
              index = Some (List.length vars);
            }
          in
          expr.node <- New (t, args, Some (Option.value_exn v.index));
          vars <- v :: vars
      | _ -> ()

    method! visit_statement stmt =
      (match stmt.node with
      | Compound _ -> self#start_scope
      | While (_, _) | DoWhile (_, _) -> self#start_scope
      | For (_, _, _, _) -> self#start_scope
      | Switch (_, _) -> self#start_scope
      | Labeled (name, _) -> self#add_label name
      | Goto _ -> self#add_goto stmt
      | Continue -> self#add_continue stmt
      | Break -> self#add_break stmt
      | _ -> ());
      super#visit_statement stmt;
      match stmt.node with
      | Compound _ -> self#end_scope ScopeAnon
      | While (_, _) | DoWhile (_, _) -> self#end_scope ScopeLoop
      | For (_, _, _, _) -> self#end_scope ScopeLoop
      | Switch (_, _) -> self#end_scope ScopeSwitch
      | _ -> ()

    method! visit_local_variable v =
      self#add_var v;
      super#visit_local_variable v

    method! visit_fundecl f =
      let conv_var index (v : variable) =
        Ain.Variable.make ~index v.name (jaf_to_ain_type v.type_spec)
      in
      let add_vars (a_f : Ain.Function.t) =
        { a_f with vars = List.mapi (List.rev vars) ~f:conv_var }
      in
      (* add params to var list *)
      List.iter f.params ~f:self#add_var;
      self#start_scope;
      super#visit_fundecl f;
      self#end_scope ScopeAnon;
      (* write updated fundecl to ain file *)
      (match Ain.get_function ctx.ain (mangled_name f) with
      | Some obj ->
          obj |> jaf_to_ain_function f |> add_vars |> Ain.write_function ctx.ain
      | None ->
          compiler_bug "Undefined function" (Some (ASTDeclaration (Function f))));
      vars <- []
  end

let allocate_variables ctx decls =
  (new variable_alloc_visitor ctx)#visit_toplevel decls
