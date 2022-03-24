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
open Jaf

let open_context file major minor import_decl =
  (* open/create the output ain file *)
  let ain =
    match file with
    | Some path -> Alice.Ain.load path
    | None -> Alice.Ain.create major minor
  in
  (* open/link the import ain files *)
  let import_ain =
    let load_import_ain base file =
      let p = Alice.Ain.load file in
      Link.link base p;
      Alice.Ain.free p
    in
    match import_decl with
    | [] -> Alice.Ain.create (Alice.Ain.version ain) (Alice.Ain.minor_version ain)
    | f::rest ->
        let base = Alice.Ain.load f in
        List.iter rest ~f:(load_import_ain base);
        base
  in
  if not (phys_equal (Alice.Ain.version ain) (Alice.Ain.version import_ain)) then
    failwith "Import .ain file version doesn't match output version";
  { ain; import_ain; const_vars=[] }

let parse_jaf jaf_file =
  let do_parse file =
    let lexbuf = Lexing.from_channel file in
    Parser.main Lexer.token lexbuf
  in
  match jaf_file with
  | Some "-" | None ->
      do_parse In_channel.stdin
  | Some path ->
      In_channel.with_file path ~f:(fun file -> do_parse file)

let compile_jaf ctx jaf_file decl_only =
  let jaf = parse_jaf jaf_file in
  Declarations.register_type_declarations ctx jaf;
  Declarations.resolve_types ctx jaf decl_only;
  Declarations.define_types ctx jaf;
  if not decl_only then begin
    TypeAnalysis.check_types ctx jaf;
    ConstEval.evaluate_constant_expressions ctx jaf;
    VariableAlloc.allocate_variables ctx jaf;
    SanityCheck.check_invariants ctx jaf; (* TODO: disable in release builds *)
    Compiler.compile ctx jaf
  end

let compile_source_files ctx output_file source_files decl_only =
  let compile_file f =
    if Filename.check_suffix f ".jaf" then
      compile_jaf ctx (Some f) decl_only
    else if Filename.check_suffix f ".ain" then
      Link.link ctx.ain (Alice.Ain.load f)
    else
      failwith "unsupported file type"
  in
  try
    begin match source_files with
    | [] -> compile_jaf ctx None decl_only
    | _ -> List.iter source_files ~f:(fun f -> compile_file f)
    end;
    Alice.Ain.write ctx.ain output_file;
    Alice.Ain.free ctx.ain
  with
  | CompileError.Type_error (expected, actual, parent) ->
      let s_expected = Alice.Ain.Type.to_string expected in
      let s_actual =
        match actual with
        | None -> "void"
        | Some expr ->
            match expr.valuetype with
            | None -> "untyped"
            | Some t -> Alice.Ain.Type.to_string t
      in
      printf "Error: Type error: expected %s; got %s\n" s_expected s_actual;
      Option.iter actual ~f:(fun e -> printf "\tat: %s\n" (expr_to_string e));
      printf "\tin: %s\n" (ast_to_string parent);
      Alice.Ain.free ctx.ain;
      exit 1
  | CompileError.Undefined_variable (name, _) ->
      printf "Error: Undefined variable: %s\n" name;
      Alice.Ain.free ctx.ain;
      exit 1
  | CompileError.Arity_error (f, args, parent) ->
      printf "Error: wrong number of arguments to function %s (expected %d; got %d)\n" f.name f.nr_args (List.length args);
      printf "\tin: %s\n" (ast_to_string parent);
      Alice.Ain.free ctx.ain;
      exit 1
  | CompileError.Not_lvalue_error (expr, parent) ->
      printf "Error: not an lvalue: %s\n" (expr_to_string expr);
      printf "\tin: %s\n" (ast_to_string parent);
      Alice.Ain.free ctx.ain;
      exit 1
  | CompileError.Const_error (var) ->
      begin match var.initval with
      | Some _ -> printf "Error: value of const variable is not constant\n"
      | None   -> printf "Error: const variable lacks initializer\n"
      end;
      printf "\tin: %s\n" (var_to_string var);
      Alice.Ain.free ctx.ain;
      exit 1
  | CompileError.CompileError (msg, node) ->
      printf "Error: %s\n" msg;
      printf "\tin: %s\n" (ast_to_string node);
      Alice.Ain.free ctx.ain;
      exit 1
  | CompileError.CompilerBug (msg, node) ->
      printf "Error: %s\n" msg;
      begin match node with
      | Some n -> printf "\tin: %s\n" (ast_to_string n)
      | None -> ()
      end;
      printf "(This is a compiler bug!)";
      Alice.Ain.free ctx.ain;
      exit 1

(* Separate Compilation
   --------------------

   ** Will require either a custom build system (pje) or to expose some esoteric
      functionality on the command line (e.g. 3.b below)

   1 Do the Declarations passes for each source file to generate source_file.types.o
   2 Combine all of the .types.o files into a single file, types.o
   3 Recompile a source file IFF:
       a. The source file was modified
       b. Any of the unresolved type definitions in the existing .o file differ
          from the corresponding definition in types.o
   4 Link all .o files into a .ain file
       * .o files are just incomplete .ain files
       * Each .o file has it's code section appended to types.o
           * A table mapping declaration indices from the .o file to the
             corresponding indices in types.o is created
           * After appending the code section, scan through every instruction
             and update indices using the created table
       * Once every .o file has been appended and updated, the output ain file
         is complete
*)

let cmd_compile_jaf =
  Command.basic
    ~summary:"Compile a .jaf file"
    ~readme: (fun () -> "Compile a .jaf file, optionally appending to an existing .ain file.")
    Command.Let_syntax.(
      let%map_open
        source_files = anon (sequence ("source files" %: Filename.arg_type))
      and ain_file = flag "-ain-file" (optional Filename.arg_type)
        ~doc:"ain-file The input .ain file"
      and output_file = flag "-output" (optional_with_default "out.ain" Filename.arg_type)
        ~doc:"out-file The output .ain file"
      and ain_version = flag "-ain-version" (optional_with_default 4 int)
        ~doc:"version The output .ain file version (default: 4)"
      and ain_minor_version = flag "-ain-minor-version" (optional_with_default 0 int)
        ~doc:"version The output .ain file minor version (default: 0)"
      and decl_only = flag "-declarations-only" no_arg
        ~doc:" Output declarations only"
      and import_decl = flag "-import-declarations" (listed Filename.arg_type)
        ~doc:"ain-file Import declarations from the given .ain file"
      in
      fun () ->
        let ctx = open_context ain_file ain_version ain_minor_version import_decl in
        compile_source_files ctx output_file source_files decl_only)

let () =
  Command.run ~version:"0.1" cmd_compile_jaf;
