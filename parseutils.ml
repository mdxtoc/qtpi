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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

open Sourcepos

exception Error of string

let parse_special entry default string =
  let lexbuf = Lexing.from_string string in
  try
    Settings.temp_setting Settings.parse_typevars true 
                          (fun () -> entry Lexer.make_token lexbuf)
  with 
  | Parsing.Parse_error ->
         (match default with 
          | Some default -> 
              let curr = lexbuf.Lexing.lex_curr_p in
              Printf.printf "\n**Parse error at character %d (just before \"%s\") \
                             when parsing string \"%s\""
                            (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)
                            (Lexing.lexeme lexbuf)
                            string;
              default
          | _            -> raise Parsing.Parse_error
         )
  | exn -> 
         (match default with
          | Some default -> 
              Printf.printf "\n**Unexpected exception %s \
                             when parsing string \"%s\""
                            (Printexc.to_string exn)
                            string;
              default
          | _            -> raise exn
         )

let parse_program filename =
  let in_channel = open_in filename in
  let lexbuf = Lexing.from_channel in_channel in
  try
    let result = Parser.program Lexer.make_token lexbuf in
    close_in in_channel; 
    result
  with
  | Parsing.Parse_error ->
      (close_in in_channel;
       let curr = lexbuf.Lexing.lex_curr_p in
       raise (Error ("**Parse error at line "^string_of_int (curr.Lexing.pos_lnum)^ 
                     " character "^string_of_int (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)^
                     " (just before \""^Lexing.lexeme lexbuf^"\")"))
                    )
  | Program.ParseError(spos,s) ->
        (close_in in_channel;
         raise (Error ("\n**SYNTAX ERROR at "^string_of_sourcepos spos ^ ": " ^ s))
        )
  | Lexer.LexError(spos,s) -> 
        (close_in in_channel;
         raise (Error ("\n**LEXING ERROR at "^string_of_sourcepos spos ^ ": " ^ s))
        )
  | exn -> (close_in in_channel; raise exn)
