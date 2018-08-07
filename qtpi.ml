(*
    Copyright (C) 2018 Richard Bornat
     
        richard@bornat.me.uk

    This file is part of Qtpi, an interpreter for Gay and Nagarajan's CQP.

    Qtpi is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    Qtpi is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Qtpi in the file LICENSE; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Settings
open Listutils
open Functionutils
open Tupleutils
open Sourcepos
open Name
open Instance
open Type
open Processdef
open Typecheck
open Resource
open Interpret
open Param

exception Error of string

let parsefile opts usage filename =
  print_endline filename; flush stdout;
  Parseutils.parse_program filename

let _ = match !Usage.files with 
        | [] -> print_string ("\nno file specified") 
        | fs -> try let defss = List.map (parsefile Usage.opts Usage.usage) (List.rev fs) in
                    let defs = List.concat defss in
                    if !verbose then
                      print_endline (string_of_list string_of_processdef "\n\n" defs);
                    typecheck defs;
                    resourcecheck defs;
                    if !Settings.interpret then
                      interpret defs
                with 
                | Interpret.Disaster (pos, s) -> Printf.printf "\n\n** interpret disaster ** %s: %s\n"
                                                               (string_of_sourcepos pos)
                                                               s
                | ResourceError (pos, s) -> Printf.printf "\n\n** %s: %s\n"
                                                          (string_of_sourcepos pos)
                                                          s
                | ResourceDisaster (pos, s) -> Printf.printf "\n\n** resource-check disaster ** %s: %s\n"
                                                          (string_of_sourcepos pos)
                                                          s
                | TypeCheckError (pos, s) -> Printf.printf "\n\n** %s: %s\n"
                                                          (string_of_sourcepos pos)
                                                          s
                | TypeUnifyError (t1, t2) -> Printf.printf "\n\n** %s cannot unify type %s with type %s\n"
                                                           (string_of_sourcepos t1.pos)
                                                           (string_of_type t1)
                                                           (string_of_type t2)
                | Parseutils.Error s     -> print_endline s
                | Library.Abandon s      -> Printf.printf "\n\n** %s -- execution abandoned\n" s
                | exn                    -> Printf.printf "\n\n** unexpected exception %s **\n"
                                                          (Printexc.to_string exn)

open Library (* pull it in, I hope *)                
