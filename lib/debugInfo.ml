(* Copyright (C) 2025 kichikuou <KichikuouChrome@gmail.com>
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
module Out_channel = Stdio.Out_channel

type debug_mapping = { addr : int; src : int; line : int }

type t = {
  mutable sources : string list;
  mutable current_src : int;
  mutable mappings : debug_mapping list;
}

let create () = { sources = []; current_src = -1; mappings = [] }

let add dbginfo addr file line =
  let src =
    match dbginfo.sources with
    | s :: _ when String.equal s file -> dbginfo.current_src
    | _ ->
        dbginfo.sources <- file :: dbginfo.sources;
        dbginfo.current_src <- dbginfo.current_src + 1;
        dbginfo.current_src
  in
  dbginfo.mappings <-
    (match dbginfo.mappings with
    | [] -> [ { addr; src; line } ]
    | last :: rest ->
        if last.addr = addr then
          (* If the last mapping has the same address, update it *)
          { addr; src; line } :: rest
        else if last.src = src && last.line = line then
          (* If the last mapping has the same source and line, keep it *)
          last :: rest
        else
          (* Otherwise, add a new mapping *)
          { addr; src; line } :: dbginfo.mappings)

let add_loc dbginfo addr (loc : Lexing.position * Lexing.position) =
  let Lexing.{ pos_fname; pos_lnum; _ } = fst loc in
  if pos_lnum <> 0 then add dbginfo addr pos_fname pos_lnum

let to_json dbginfo =
  let sources = List.rev_map dbginfo.sources ~f:(fun s -> `String s) in
  let mappings =
    List.rev_map dbginfo.mappings ~f:(fun { addr; src; line } ->
        `List [ `Int addr; `Int src; `Int line ])
  in
  `Assoc
    [
      ("version", `String "alpha-1");
      ("sources", `List sources);
      ("mappings", `List mappings);
    ]

let write_to_file dbginfo file = Yojson.Basic.to_file file (to_json dbginfo)
