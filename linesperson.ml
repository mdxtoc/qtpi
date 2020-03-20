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
open Parserparams
open Optionutils
open Sourcepos

let token = ref Parser.EOP
let ready = ref false

let make_make_token : Sedlexing.lexbuf -> (Sedlexing.lexbuf -> Parser.token) = fun lexbuf ->
  let get_token () = token := Lexer.make_token lexbuf;
                     let start_pos, end_pos = Sedlexing.lexing_positions lexbuf in
                     curr_start := offset_of_position start_pos;
                     curr_end := offset_of_position end_pos;
                     if !verbose || !verbose_offside then 
                       Printf.eprintf "Linesperson.get_token read %s (%s)\n"
                                        (Lexer.string_of_token !token)
                                        (short_string_of_sourcepos (Sedlexing.lexing_positions lexbuf));
                     while !push_pending > 0 do
                       do_push_offsideline !curr_start;
                       push_pending := !push_pending-1
                     done;
                     ready := true
  in
  (* initialise *)
  init_offside ();
  ready := false;
  let make_token lexbuf =
    if not !ready then get_token ();
    if is_offside () then 
      (if !verbose || !verbose_offside then 
         let start_p, _ = Sedlexing.lexing_positions lexbuf in
         Printf.eprintf "offside (%d) at line %d, char %d\n" 
                       !offsideline
                       (Sourcepos.linenum start_p)
                       (Sourcepos.charnum start_p)
       else ();
       Parser.OFFSIDE
      ) 
    else 
      (ready := false; 
       if !verbose || !verbose_offside then
         Printf.eprintf "Linesperson.make_token provides %s (%s)\n"
                          (Lexer.string_of_token !token)
                          (short_string_of_sourcepos (Sedlexing.lexing_positions lexbuf));       
      !token
      )
  in
  make_token
  