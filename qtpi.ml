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
open Def
open Typecheck
open Matchcheck
open Resource
open Interpret
open Param

exception Error of string

let parsefile opts usage filename =
  Parseutils.parse_program filename

let _ = match !Usage.files with 
        | [] -> print_string ("\nno file specified") 
        | fs -> try (* check the library has parseable types *)
                    (try List.iter (fun (n,s,v) -> ignore (Parseutils.parse_typestring s)) !Interpret.knowns
                     with Parseutils.Error s -> raise (Parseutils.Error ("while checking types in built-in library: " ^ s))
                    );
                    let defss = List.map (parsefile Usage.opts Usage.usage) (List.rev fs) in
                    let defs = List.concat defss in
                    if !verbose then
                      print_endline (string_of_list string_of_def "\n\n" defs);
                    typecheck defs;
                    matchcheck defs;
                    if !Settings.resourcecheck then
                      Resource.resourcecheck defs;
                    if !Settings.interpret then
                      interpret defs;
                    if !Settings.checkrandombias then
                      (Printf.printf "randbit bias %s/%s; measure bias %s/%s\n"
                                            (Number.string_of_num !Library._zeroes) (Number.string_of_num !Library._ones)
                                            (Number.string_of_num !Qsim._zeroes) (Number.string_of_num !Qsim._ones)
                      )
                with 
                | Interpret.Disaster (pos, s) -> Printf.printf "\n\n** interpret disaster ** %s: %s\n"
                                                               (string_of_sourcepos pos)
                                                               s
                | Interpret.Error (pos, s) -> Printf.printf "\n\n** execution error %s: %s\n"
                                                            (string_of_sourcepos pos)
                                                            s
                | Interpret.MatchError (pos, s) -> Printf.printf "\n\n** match error %s: %s\n"
                                                                 (string_of_sourcepos pos)
                                                                 s
                | Qsim.Error s -> Printf.printf "\n\n** quantum simulator error %s\n" s
                | Resource.Error (pos, s) -> Printf.printf "\n\n** %s: %s\n"
                                                          (string_of_sourcepos pos)
                                                          s
                | Resource.Disaster (pos, s) -> Printf.printf "\n\n** resource-check disaster ** %s: %s\n"
                                                          (string_of_sourcepos pos)
                                                          s
                | Type.Error (pos, s) -> Printf.printf "\n\n** %s: %s\n"
                                                            (string_of_sourcepos pos)
                                                            s
                | Typecheck.Error (pos, s) -> Printf.printf "\n\n** %s: %s\n"
                                                            (string_of_sourcepos pos)
                                                            s
                | TypeUnifyError (outer, inner) -> Printf.printf "\n\n** type %s (%s) doesn't fit in type %s (%s)\n"
                                                           (string_of_type inner)
                                                           (string_of_sourcepos inner.pos)
                                                           (string_of_type outer)
                                                           (string_of_sourcepos outer.pos)
                | Parseutils.Error s     -> print_endline s
                | Library.Abandon s      -> Printf.printf "\n\n** %s -- execution abandoned\n" s
                | Settings.Can'tHappen s -> Printf.printf "!! Can't Happen !! -- %s" s
                | exn                    -> Printf.printf "\n\n** unexpected exception %s **\n"
                                                          (Printexc.to_string exn)

open Library (* pull it in, I hope *)                
