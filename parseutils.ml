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
open Sourcepos

exception Error of string

(* In order to use a sedlex lexer with a Menhir (or indeed an ocamlyacc) parser, 
   it is necessary to do a peculiar dance. This is that dance, taken from
    https://stackoverflow.com/questions/52474076/using-ocamlyacc-with-sedlex
 *)
 
 let provider make_token lexbuf () =
    let tok = make_token lexbuf in
    let start, stop =  Sedlexing.lexing_positions lexbuf in
    tok, start, stop

 let parser entry lexbuf = MenhirLib.Convert.Simplified.traditional2revised
     entry (provider (Linesperson.make_make_token lexbuf) lexbuf)

(* end of dance *)

let parse_string entry string =
  let lexbuf = Sedlexing.from_gen (Utf8.from_string string) in
  Sedlexing.set_filename lexbuf "";
  Sedlexing.set_position lexbuf {Lexing.pos_fname=""; Lexing.pos_lnum=1; Lexing.pos_bol=0; Lexing.pos_cnum=0};
  try
    parser entry lexbuf
  with 
  | Parsing.Parse_error 
  (* for menhir | Parser.Error *) ->
         (let curr, _ = Sedlexing.lexing_positions lexbuf in
          raise (Error (Printf.sprintf "**Parse error at character %d (just before \"%s\") \
                                        when parsing string \"%s\""
                                       (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)
                                       (Lexer.string_of_lexeme (Sedlexing.lexeme lexbuf))
                                       string
                       )
                )
         )
  | Lexer.LexError(spos,s) -> 
        (raise (Error (Printf.sprintf "\n**%s: LEXING ERROR: %s \
                                       when parsing string \"%s\""
                                      (string_of_stringpos spos)
                                      s
                                      string
                      )
               )
        )
  | exn -> 
        raise (Error (Printf.sprintf "**Unexpected exception %s \
                                      when parsing string \"%s\""
                                     (Printexc.to_string exn)
                                     string
                     )
              )

let parse_typestring s = parse_string Parser.readtype s

let parse_exprstring s = parse_string Parser.readexpr s

let parse_pdefstring s = parse_string Parser.readpdef s

let parse_program filename =
  let in_channel = try open_in filename with Sys_error s -> raise (Error ("** " ^ s)) in
  let lexbuf = Sedlexing.from_gen (Utf8.from_channel in_channel) in
  Sedlexing.set_filename lexbuf filename;
  Sedlexing.set_position lexbuf {Lexing.pos_fname=filename; Lexing.pos_lnum=1; Lexing.pos_bol=0; Lexing.pos_cnum=0};
  try
    let result = parser Parser.program lexbuf in
    close_in in_channel; 
    result
  with
  | Parsing.Parse_error 
  (* for menhir | Parser.Error *) ->
      (close_in in_channel;
       let curr, _ = Sedlexing.lexing_positions lexbuf in
       raise (Error (Printf.sprintf "\n** %s: Parse error at line %d character %d (just before \"%s\")\n"
                                    filename
                                    (curr.Lexing.pos_lnum)
                                    (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)
                                    (Lexer.string_of_lexeme (Sedlexing.lexeme lexbuf))
                    )
             )
      )
  | Program.ParseError(spos,s) ->
        (close_in in_channel;
         raise (Error (Printf.sprintf "\n** %s: SYNTAX ERROR: %s\n"
                                      (string_of_sourcepos spos)
                                      s
                      )
               )
        )
  | Lexer.LexError(spos,s) -> 
        (close_in in_channel;
         raise (Error (Printf.sprintf "\n**%s: LEXING ERROR: %s\n"
                                      (string_of_sourcepos spos)
                                      s
                      )
               )
        )
  | exn -> (close_in in_channel; raise exn)
