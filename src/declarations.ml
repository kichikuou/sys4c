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

(*
 * AST pass over top-level declarations register names in the .ain file.
 *)
class type_declare_visitor ctx =
  object (self)
    inherit ivisitor ctx
    val functions = Stack.create ()

    method declare_function decl =
      let name = mangled_name decl in
      (match Ain.get_function ctx.ain name with
      | Some _ ->
          compile_error "Duplicate function definition"
            (ASTDeclaration (Function decl))
      | None -> decl.index <- Some (Ain.add_function ctx.ain name).index);
      Stack.push functions decl

    method! visit_declaration decl =
      match decl with
      | Global g ->
          if not g.is_const then (
            if Option.is_some (Ain.get_global ctx.ain g.name) then
              compile_error "duplicate global variable definition"
                (ASTDeclaration decl);
            g.index <- Some (Ain.add_global ctx.ain g.name))
      | Function f -> self#declare_function f
      | FuncTypeDef f ->
          if Option.is_some (Ain.get_functype ctx.ain f.name) then
            compile_error "duplicate functype definition" (ASTDeclaration decl);
          ignore (Ain.add_functype ctx.ain f.name : Ain.FunctionType.t)
      | DelegateDef f ->
          if Option.is_some (Ain.get_delegate ctx.ain f.name) then
            compile_error "duplicate delegate definition" (ASTDeclaration decl);
          ignore (Ain.add_delegate ctx.ain f.name : Ain.FunctionType.t)
      | StructDef s ->
          if Option.is_some (Ain.get_struct ctx.ain s.name) then
            compile_error "duplicate struct definition" (ASTDeclaration decl);
          let ain_s = Ain.add_struct ctx.ain s.name in
          let visit_decl = function
            | AccessSpecifier _ -> ()
            | Constructor f ->
                if not (String.equal f.name s.name) then
                  compile_error "constructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.name <- s.name ^ "@0";
                f.class_index <- Some ain_s.index;
                self#declare_function f
            | Destructor f ->
                if not (String.equal f.name s.name) then
                  compile_error "destructor name doesn't match struct name"
                    (ASTDeclaration (Function f));
                f.name <- s.name ^ "@1";
                f.class_index <- Some ain_s.index;
                self#declare_function f
            | Method f ->
                f.name <- s.name ^ "@" ^ f.name;
                f.class_index <- Some ain_s.index;
                self#declare_function f
            | MemberDecl _ -> ()
          in
          List.iter s.decls ~f:visit_decl
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl)
  end

let register_type_declarations ctx decls =
  (new type_declare_visitor ctx)#visit_toplevel decls

(*
 * AST pass to resolve user-defined types (struct/enum/function types).
 *)
class type_resolve_visitor ctx decl_only =
  object (self)
    inherit ivisitor ctx as super

    method resolve_type name node =
      match Ain.get_struct_index ctx.ain name with
      | Some i -> Struct (name, i)
      | None -> (
          match Ain.get_functype_index ctx.ain name with
          | Some i -> FuncType (name, i)
          | None -> (
              match Ain.get_delegate_index ctx.ain name with
              | Some i -> Delegate (name, i)
              | None -> compile_error ("Undefined type: " ^ name) node))

    method resolve_typespec ts node =
      let rec resolve t =
        match t with
        | Unresolved t -> self#resolve_type t node
        | Ref t -> Ref (resolve t)
        | Array t -> Array (resolve t)
        | Wrap t -> Wrap (resolve t)
        | _ -> t
      in
      resolve ts

    method! visit_expression expr =
      (match expr.node with
      | New (Unresolved t, e, _) ->
          expr.node <- New (self#resolve_type t (ASTExpression expr), e, None)
      | _ -> ());
      super#visit_expression expr

    method! visit_local_variable decl =
      decl.ty <- self#resolve_typespec decl.ty (ASTVariable decl);
      super#visit_local_variable decl

    method! visit_declaration decl =
      let function_class (f : fundecl) =
        match f.struct_name with
        | Some name -> Ain.get_struct_index ctx.ain name
        | _ -> None
      in
      let resolve_function f =
        f.return_ty <-
          self#resolve_typespec f.return_ty (ASTDeclaration (Function f));
        List.iter f.params ~f:(fun v ->
            v.ty <- self#resolve_typespec v.ty (ASTVariable v))
      in
      (match decl with
      | Function f ->
          resolve_function f;
          f.class_index <- function_class f
      | FuncTypeDef f | DelegateDef f -> resolve_function f
      | Global g -> g.ty <- self#resolve_typespec g.ty (ASTDeclaration decl)
      | StructDef s ->
          let resolve_structdecl = function
            | AccessSpecifier _ -> ()
            | MemberDecl d ->
                d.ty <- self#resolve_typespec d.ty (ASTDeclaration decl)
            | Constructor f | Destructor f | Method f -> resolve_function f
          in
          List.iter s.decls ~f:resolve_structdecl
      | Enum _ ->
          compile_error "enum types not yet supported" (ASTDeclaration decl));
      if not decl_only then super#visit_declaration decl
  end

let resolve_types ctx decls decl_only =
  (new type_resolve_visitor ctx decl_only)#visit_toplevel decls

(*
 * AST pass over top-level declarations to define function/struct types.
 *)
class type_define_visitor ctx =
  object
    inherit ivisitor ctx

    method! visit_declaration decl =
      match decl with
      | Global g ->
          if g.is_const then ctx.const_vars <- g :: ctx.const_vars
          else Ain.set_global_type ctx.ain g.name (jaf_to_ain_type g.ty)
      | Function f ->
          let obj =
            Ain.get_function_by_index ctx.ain (Option.value_exn f.index)
          in
          obj |> jaf_to_ain_function f |> Ain.write_function ctx.ain
      | FuncTypeDef f -> (
          match Ain.get_functype ctx.ain f.name with
          | Some obj ->
              obj |> jaf_to_ain_functype f |> Ain.write_functype ctx.ain
          | None ->
              compiler_bug "undefined functype" (Some (ASTDeclaration decl)))
      | DelegateDef f -> (
          match Ain.get_delegate ctx.ain f.name with
          | Some obj ->
              obj |> jaf_to_ain_functype f |> Ain.write_delegate ctx.ain
          | None ->
              compiler_bug "undefined delegate" (Some (ASTDeclaration decl)))
      | StructDef s -> (
          match Ain.get_struct ctx.ain s.name with
          | Some obj -> obj |> jaf_to_ain_struct s |> Ain.write_struct ctx.ain
          | None -> compiler_bug "undefined struct" (Some (ASTDeclaration decl))
          )
      | Enum _ ->
          compile_error "Enum types not yet supported" (ASTDeclaration decl)
  end

let define_types ctx decls = (new type_define_visitor ctx)#visit_toplevel decls

let define_library ctx decls name =
  let is_struct_def decl = match decl with StructDef _ -> true | _ -> false in
  let struct_defs, fun_decls = List.partition_tf decls ~f:is_struct_def in
  (* handle struct definitions *)
  register_type_declarations ctx struct_defs;
  resolve_types ctx struct_defs true;
  define_types ctx struct_defs;
  (* define library *)
  let functions =
    List.map fun_decls ~f:(function
      | Function f -> jaf_to_ain_hll_function f
      | decl ->
          compiler_bug "unexpected declaration in .hll file"
            (Some (ASTDeclaration decl)))
  in
  let lib = { (Ain.add_library ctx.ain name) with functions } in
  Ain.write_library ctx.ain lib
