(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
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

exception KeyError of string

type formation = { name : string; defs : string list }

type t = {
  mutable pje_path : string;
  mutable encoding : string;
  mutable project_name : string;
  mutable code_name : string;
  mutable game_version : int;
  mutable source_dir : string;
  mutable hll_dir : string;
  mutable obj_dir : string;
  mutable output_dir : string;
  mutable source : source list;
  mutable system_source : source list;
  mutable hll : string list;
  mutable copy_to_dll : string list;
  mutable copy_to_run : string list;
  mutable copy_to_dp : string list;
  mutable sync_folder : (string * string) list;
  mutable scenario_func_a : string list;
  mutable scenario_func_r : string list;
  mutable scenario_func_name : string list;
  mutable formations : formation list;
  mutable sync_lock : bool;
  mutable update_ide_path : string option;
  (* AinDecompiler extensions *)
  mutable ain_version : int;
  mutable key_code : int;
  mutable is_ai2_file : bool;
  mutable uses_msg1 : bool;
  mutable target_vm : int;
}

and source = Jaf of string | Hll of (string * string) | Include of t

let default_pje path =
  {
    pje_path = path;
    encoding = "UTF-8";
    project_name = "";
    code_name = "code.jab";
    game_version = 100;
    source_dir = ".";
    hll_dir = ".";
    obj_dir = ".";
    output_dir = ".";
    source = [];
    system_source = [];
    hll = [];
    copy_to_dll = [];
    copy_to_run = [];
    copy_to_dp = [];
    sync_folder = [];
    scenario_func_a = [];
    scenario_func_r = [];
    scenario_func_name = [];
    formations = [];
    sync_lock = false;
    update_ide_path = None;
    ain_version = 4;
    key_code = 0;
    is_ai2_file = false;
    uses_msg1 = false;
    target_vm = 0;
  }

let collect_sources pje =
  let rec collect acc = function
    | [] -> acc
    | Include inc :: rest ->
        collect (collect acc (inc.system_source @ inc.source)) rest
    | item :: rest -> collect (item :: acc) rest
  in
  collect [] (pje.system_source @ pje.source) |> List.rev

let ain_path pje =
  let open Stdlib.Filename in
  concat (dirname pje.pje_path) (concat pje.output_dir pje.code_name)

let debug_info_path pje =
  let open Stdlib.Filename in
  concat (dirname pje.pje_path) "debug_info.json"
