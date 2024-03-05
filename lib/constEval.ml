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
open CompileError

let expr_replace (dst : expression) (expr : expression) =
  dst.ty <- expr.ty;
  dst.node <- expr.node

let const_replace (dst : expression) const_expr =
  dst.ty <-
    (match const_expr with
    | ConstInt _ -> Int
    | ConstFloat _ -> Float
    | ConstChar _ -> Int
    | ConstString _ -> String
    | _ ->
        compiler_bug "const_replace: not a constant expression"
          (Some
             (ASTExpression { node = const_expr; ty = Untyped; loc = dst.loc })));
  dst.node <- const_expr

let const_binary dst a b int_op float_op string_op =
  match (a, b) with
  | ConstInt i_a, ConstInt i_b -> (
      match int_op with
      | Some iop -> const_replace dst (ConstInt (iop i_a i_b))
      | None -> ())
  | ConstFloat f_a, ConstFloat f_b -> (
      match float_op with
      | Some fop -> const_replace dst (ConstFloat (fop f_a f_b))
      | None -> ())
  | ConstString s_a, ConstString s_b -> (
      match string_op with
      | Some sop -> const_replace dst (ConstString (sop s_a s_b))
      | None -> ())
  | _ -> ()

let const_compare dst a b int_op float_op =
  match a with
  | ConstInt i_a -> (
      match b with
      | ConstInt i_b -> const_replace dst (ConstInt (int_op i_a i_b))
      | _ -> ())
  | ConstFloat f_a -> (
      match b with
      | ConstFloat f_b -> const_replace dst (ConstInt (float_op f_a f_b))
      | _ -> ())
  | _ -> ()

let const_unary dst e int_op float_op =
  match e with
  | ConstInt i -> (
      match int_op with
      | Some iop -> const_replace dst (ConstInt (iop i))
      | None -> ())
  | ConstFloat f -> (
      match float_op with
      | Some fop -> const_replace dst (ConstFloat (fop f))
      | None -> ())
  | _ -> ()

class const_eval_visitor ctx =
  object (self)
    inherit ivisitor ctx as super
    val mutable in_initval = false

    method eval_expression (expr : expression) =
      match expr.node with
      | ConstInt _ -> ()
      | ConstFloat _ -> ()
      | ConstChar _ -> ()
      | ConstString _ -> ()
      | Ident (name, _) -> (
          match environment#resolve name with
          | ResolvedLocal v | ResolvedGlobal v | ResolvedMember (_, v) -> (
              if v.is_const then
                match v.initval with
                | Some e -> const_replace expr e.node
                | None -> const_error v)
          | _ -> ())
      | Unary (op, e) -> (
          let const_not i = if i = 0 then 1 else 0 in
          match op with
          | UPlus ->
              const_unary expr e.node (Some Stdlib.( ~+ )) (Some Stdlib.( ~+. ))
          | UMinus -> const_unary expr e.node (Some ( ~- )) (Some ( ~-. ))
          | LogNot -> const_unary expr e.node (Some const_not) None
          | BitNot -> const_unary expr e.node (Some lnot) None
          | AddrOf -> ()
          | PreInc -> ()
          | PreDec -> ()
          | PostInc -> ()
          | PostDec -> ())
      | Binary (op, a, b) -> (
          let mk_compare op a b = if op a b then 1 else 0 in
          let const_eq = mk_compare ( = ) in
          let const_neq a b = if a = b then 0 else 1 in
          let const_lt = mk_compare ( < ) in
          let const_gt = mk_compare ( > ) in
          let const_lte = mk_compare ( <= ) in
          let const_gte = mk_compare ( >= ) in
          let const_feq = mk_compare Float.equal in
          let const_fneq a b = if Float.equal a b then 0 else 1 in
          let const_flt = mk_compare Float.( < ) in
          let const_fgt = mk_compare Float.( > ) in
          let const_flte = mk_compare Float.( <= ) in
          let const_fgte = mk_compare Float.( >= ) in
          let const_logor a b =
            if not (a = 0) then a else if not (b = 0) then b else 0
          in
          let const_logand a b =
            if not (a = 0) then if not (b = 0) then 1 else 0 else 0
          in
          match op with
          | Plus ->
              const_binary expr a.node b.node (Some ( + )) (Some ( +. ))
                (if in_initval then Some ( ^ ) else None)
          | Minus ->
              const_binary expr a.node b.node (Some ( - )) (Some ( -. )) None
          | Times ->
              const_binary expr a.node b.node (Some ( * )) (Some ( *. )) None
          | Divide ->
              const_binary expr a.node b.node (Some ( / )) (Some ( /. )) None
          | Modulo ->
              const_binary expr a.node b.node (Some Stdlib.( mod )) None None
          | Equal -> const_compare expr a.node b.node const_eq const_feq
          | NEqual -> const_compare expr a.node b.node const_neq const_fneq
          | LT -> const_compare expr a.node b.node const_lt const_flt
          | GT -> const_compare expr a.node b.node const_gt const_fgt
          | LTE -> const_compare expr a.node b.node const_lte const_flte
          | GTE -> const_compare expr a.node b.node const_gte const_fgte
          | LogOr ->
              const_binary expr a.node b.node (Some const_logor) None None
          | LogAnd ->
              const_binary expr a.node b.node (Some const_logand) None None
          | BitOr -> const_binary expr a.node b.node (Some ( lor )) None None
          | BitXor -> const_binary expr a.node b.node (Some ( lxor )) None None
          | BitAnd -> const_binary expr a.node b.node (Some ( land )) None None
          | LShift -> const_binary expr a.node b.node (Some ( lsl )) None None
          | RShift -> const_binary expr a.node b.node (Some ( lsr )) None None
          | RefEqual | RefNEqual -> ())
      | Assign (_, _, _) -> ()
      | Seq (_, _) -> ()
      | Ternary (test, con, alt) -> (
          match test.node with
          | ConstInt 0 -> expr_replace expr alt
          | ConstInt _ -> expr_replace expr con
          | _ -> ())
      | Cast (t, e) -> (
          match t with
          | Int | LongInt -> (
              match e.node with
              | ConstInt _ -> const_replace expr e.node
              | ConstFloat f -> const_replace expr (ConstInt (Int.of_float f))
              | ConstChar _ -> () (* TODO? *)
              | _ -> ())
          | Bool when in_initval -> (
              match e.node with
              | ConstInt i ->
                  const_replace expr (ConstInt (if i = 0 then 0 else 1))
              | _ -> ())
          | Float -> (
              match e.node with
              | ConstInt i -> const_replace expr (ConstFloat (Float.of_int i))
              | ConstFloat _ -> const_replace expr e.node
              | ConstChar _ -> () (* TODO? *)
              | _ -> ())
          | _ -> ())
      | Subscript (_, _) -> ()
      | Member (_, name, ClassConst struct_name) -> (
          let struc = Hashtbl.find_exn ctx.structs struct_name in
          let v = Hashtbl.find_exn struc.members name in
          match v.initval with
          | Some e -> const_replace expr e.node
          | None -> const_error v)
      | Member (_, _, _) -> ()
      | Call (_, _, _) -> ()
      | New _ -> ()
      | DummyRef _ -> ()
      | This -> ()
      | Null -> ()

    method! visit_toplevel decls =
      (* XXX: evaluate all global constants first *)
      Hashtbl.iter ctx.globals ~f:(fun g ->
          if g.is_const then
            match g.initval with
            | Some expr -> self#eval_expression expr
            | None -> const_error g);
      super#visit_toplevel decls

    method! visit_expression expr =
      super#visit_expression expr;
      self#eval_expression expr

    method! visit_variable v =
      in_initval <-
        Option.is_some v.initval && (Poly.(v.kind <> LocalVar) || v.is_const);
      super#visit_variable v;
      in_initval <- false;
      if v.is_const then
        match v.initval with
        | Some e -> (
            match e.node with
            | ConstInt _ -> ()
            | ConstFloat _ -> ()
            | ConstChar _ -> ()
            | ConstString _ -> ()
            | _ -> const_error v)
        | None -> const_error v
      else
        match (v.kind, v.initval) with
        | GlobalVar, Some e ->
            Ain.set_global_initval ctx.ain v.name
              (match e.node with
              | ConstInt i -> Ain.Variable.Int (Int32.of_int_exn i)
              | ConstFloat f -> Ain.Variable.Float f
              | ConstString s -> Ain.Variable.String s
              | _ -> const_error v)
        | Parameter, Some e -> (
            match e.node with
            | ConstInt _ | ConstFloat _ | ConstChar _ | ConstString _ | Null ->
                ()
            | _ -> const_error v)
        | _ -> ()
  end

let evaluate_constant_expressions ctx decls =
  (new const_eval_visitor ctx)#visit_toplevel decls
