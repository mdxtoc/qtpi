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
 
{
  open Parser
  
  exception LexError of Sourcepos.sourcepos * string
    
  let inc_linenum lexbuf =
  	let curr = lexbuf.Lexing.lex_curr_p in
  	lexbuf.Lexing.lex_curr_p <- 
  		{ lexbuf.Lexing.lex_curr_p with Lexing.pos_lnum = curr.Lexing.pos_lnum+1;
  										Lexing.pos_bol = curr.Lexing.pos_cnum
  		}
  
  let get_linenum lexbuf = 
  	let curr = lexbuf.Lexing.lex_curr_p in
  	curr.Lexing.pos_lnum
  	
  let get_loc lexbuf =
  	(Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

}

let BLANK = [' ' '\t']
let NEWLINE = '\n'
let LINE = [^ '\n']* ('\n' | eof)

let NUM = ['0'-'9']
let ALPHA =  ['a'-'z'] | ['A'-'Z']
let ALPHANUM = ALPHA | NUM | '_' 

let number = NUM+

let name   = ('_' | ALPHA) (ALPHA | NUM | '_' | '\'')*

let eol = '\n'

rule make_token = parse

  | BLANK       { make_token lexbuf} (* Skip blanks and tabs *)
  | NEWLINE     { inc_linenum lexbuf; make_token lexbuf}
  | "(*"   		{ bracomment (get_loc lexbuf) lexbuf; make_token lexbuf }

  | eof         {EOP}   (* Give up on end of file *)

  | '('         {LPAR}
  | ')'         {RPAR}
  | '{'         {LBRACE}
  | '}'         {RBRACE}
  | '['         {LSQPAR}
  | ']'         {RSQPAR}
  | '|'         {BAR}
  | ':'         {COLON}
  | '='         {EQUALS}
  | '*'         {STAR}
  
  | "true"      {TRUE}
  | "false"     {FALSE}
  
  | "if"        {IF}
  | "then"      {THEN}
  | "else"      {ELSE}
  | "fi"        {FI}
    
  | "int"       {INTTYPE}
  | "bool"      {BOOLTYPE}
  | "bit"       {BITTYPE}
  | "unit"      {UNITTYPE}
  | "qbit"      {QBITTYPE}
  | "^"         {CHANTYPE}
  | "list"      {LISTTYPE}
  
  | '.'         {DOT}
  | ".."        {DOTDOT}
    
  | "_H"        {HADAMARD}
  | "_I"        {I}
  | "_X"        {X}
  | "_Cnot"     {CNOT}
  | "_CNot"     {CNOT}
  | "_CNOT"     {CNOT}
  | "_Phi"      {PHI}
  | "_PHI"      {PHI}
  | "new"       {NEWDEC}
  (* do we need dispose? *)
  | "newq"      {QBITDEC}
  
  | '?'         {QUERY}
  | '!'         {BANG}
  | "??"        {MEASURE}
  | ">>"        {THROUGH}
  
  | ','         {COMMA}
  | ';'         {SEMICOLON}
  
  | "++"        {PLUSPLUS}
  | '+'         {PLUS}
  | '-'         {MINUS}
  
  | '='         {EQUALS}
  | "<>"        {NOTEQUAL}
  
  | "&&"        {AND}
  | "||"        {OR}

  | '@'         {APPEND}
      
(* | '_'        {UNDERSCORE} *)
  
  | "_0"        {TERMINATE}
  
  | "0b0"       {BIT0}
  | "0b1"       {BIT1}
  
  | "All"       {FORALL}
  | "process"   {PROCESS}
  
  | "->"        {TYPEARROW}
  | "'"         {PRIME}
  
  | "given"     {GIVEN}

  | number      {INT (Lexing.lexeme lexbuf)}
  | name        {NAME (Lexing.lexeme lexbuf)}    (* should be interned *)

  | _           {raise (LexError (get_loc lexbuf, "Invalid character '" ^ 
                                                  Lexing.lexeme lexbuf ^ 
                                                  "'"
                                 )
                       )
                }

and bracomment spos = parse
	|	"(*"        { bracomment (get_loc lexbuf) lexbuf; 
					  bracomment spos lexbuf
					}
  	| 	"*)"        { () }
  	| 	'\n'        { inc_linenum lexbuf; bracomment spos lexbuf }
  	|	eof			{ raise (LexError (spos, "unmatched comment-bracket '(*'")) }
  	| 	_           { bracomment spos lexbuf }
      
{

let build_prog_from_string s =
  Parser.program make_token (Lexing.from_string s)

}
