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

let token = ref Parser.EOP
let ready = ref false

let make_make_token lexbuf =
  let get_token () = token := Lexer.make_token lexbuf;
                     curr_start := offset_of_position (Lexing.lexeme_start_p lexbuf);
                     curr_end := offset_of_position (Lexing.lexeme_end_p lexbuf);
                     ready := true
  in
  (* initialise *)
  init_offside ();
  ready := false;
  let make_token lexbuf =
    if not !ready then get_token ();
    if is_offside () then 
      (if !verbose then 
         let start_p = Lexing.lexeme_start_p lexbuf in
         Printf.printf "offside (%d) at line %d, char %d\n" 
                       !offsideline
                       (Sourcepos.linenum start_p)
                       (Sourcepos.charnum start_p)
       else ();
       Parser.OFFSIDE
      ) 
    else (ready := false; !token)
  in
  make_token
  