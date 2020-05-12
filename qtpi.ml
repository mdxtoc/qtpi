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

let _ = ((match !Usage.files with 
          | [] -> print_string ("\nno file specified") 
          | fs -> try (* check the library has parseable types *)
                      (try List.iter (fun (n,s,v) -> ignore (Parseutils.parse_typestring s)) !Library.knowns
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
                        Number.(Printf.printf "randbit bias %s/%s; measure bias %s/%s\n"
                                                     (string_of_zint !Library._zeroes) (string_of_zint !Library._ones)
                                                     (string_of_zint !Qsim._zeroes) (string_of_zint !Qsim._ones)
                               );
                      exit 0
                  with 
                  | Interpret.Disaster (pos, s) -> Printf.eprintf "\n\n** interpret disaster ** %s: %s\n"
                                                                 (string_of_sourcepos pos)
                                                                 s
                  | Interpret.Error (pos, s) -> Printf.eprintf "\n\n** execution error %s: %s\n"
                                                              (string_of_sourcepos pos)
                                                              s
                  | Interpret.MatchError (pos, s) -> Printf.eprintf "\n\n** match error %s: %s\n"
                                                                   (string_of_sourcepos pos)
                                                                   s
                  | Qsim.Error s -> Printf.eprintf "\n\n** quantum simulator error %s\n" s
                  | Compile.CompileError   (pos, s) 
                  | Compile.ExecutionError   (pos, s) 
                  | Expr.Error      (pos, s) 
                  | Type.Error      (pos, s) 
                  | Resource.Error  (pos, s) 
                  | Typecheck.Error (pos, s) -> Printf.eprintf "\n\n** %s: %s\n"
                                                            (string_of_sourcepos pos)
                                                            s
                  | Resource.Disaster (pos, s) -> Printf.eprintf "\n\n** resource-check disaster ** %s: %s\n"
                                                            (string_of_sourcepos pos)
                                                            s
                  | TypeUnifyError (outer, inner) -> Printf.eprintf "\n\n** type %s (%s) doesn't fit in type %s (%s)\n"
                                                             (string_of_type inner)
                                                             (string_of_sourcepos inner.pos)
                                                             (string_of_type outer)
                                                             (string_of_sourcepos outer.pos)
                  | Parseutils.Error s     -> prerr_endline s
                  | Library.Abandon s      -> Printf.eprintf "\n\n** %s -- execution abandoned\n" s
                  | Settings.Can'tHappen s -> Printf.eprintf "!! Can't Happen !! -- %s" s
                  | Snum.Disaster s        -> Printf.eprintf "** Calculator disaster: %s **\n" s
                  | Vmg.Error s            -> Printf.eprintf "** Vector/matrix algebra error: %s **\n" s
                  | exn                    -> Printf.eprintf "\n\n** unexpected exception %s **\n"
                                                            (Printexc.to_string exn)
         ); (* end of match *)
         exit 1
        )
        
open Library (* pull it in, I hope *)                
