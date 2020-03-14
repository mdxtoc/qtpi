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
 
type sourcepos = string * Lexing.position * Lexing.position (* filename, line num, char num *)

let dummy_spos = ("", Lexing.dummy_pos, Lexing.dummy_pos)

let linenum lpos = lpos.Lexing.pos_lnum
let charnum lpos = lpos.Lexing.pos_cnum-lpos.Lexing.pos_bol

let string_of_sourcepos spos = 
  if spos = dummy_spos then "_" else
  let filename, startpos,endpos = spos in
  if linenum startpos=linenum endpos then
    Printf.sprintf "%s line %d chars %d-%d" 
      filename (linenum startpos) (charnum startpos) (charnum endpos)
  else
    Printf.sprintf "%s line %d char %d - line %d char %d"
      filename
      (linenum startpos) (charnum startpos)
      (linenum endpos) (charnum endpos)

let string_of_stringpos spos = 
  if spos = dummy_spos then "_" else
  let _, startpos, endpos = spos in
    Printf.sprintf "chars %d-%d" 
      (charnum startpos) (charnum endpos)

let startline (_,startpos,endpos) = linenum startpos
let endline   (_,startpos,endpos) = linenum endpos

let startchar (_,startpos,endpos) = charnum startpos
let endchar   (_,startpos,endpos) = charnum endpos

let short_string_of_sourcepos (_,startpos,endpos) = 
  if linenum startpos=linenum endpos then
    Printf.sprintf "%d.%d-%d"
                   (linenum startpos) (charnum startpos) (charnum endpos)    
  else
    Printf.sprintf "%d.%d-%d%d"
      (linenum startpos) (charnum startpos)
      (linenum endpos) (charnum endpos)

let startsbefore pos1 pos2 = startline pos1 < startline pos2 || 
                             (startline pos1 = startline pos2 && startchar pos1 < startchar pos2)

let endsbefore pos1 pos2 = endline pos1 < endline pos2 || 
                           (endline pos1 = endline pos2 && endchar pos1 < endchar pos2)

let spos_of_spos2 pos1 pos2 =
  if pos1=dummy_spos then pos2 else
  if pos2=dummy_spos then pos1 else
    let fst = if startsbefore pos1 pos2 then pos1 else pos2 in
    let snd = if endsbefore pos1 pos2 then pos2 else pos1 in
    match fst, snd with
    | (fn,startpos,_), (_,_,endpos) -> (fn,startpos, endpos)


let sp_of_sps sps = 
  let rec enclosing spos = function
    | []      -> spos
    | sp::sps -> enclosing (spos_of_spos2 spos sp) sps
  in
  enclosing dummy_spos sps

let spdiff pos1 pos2 =
  match pos1, pos2 with
  | (fn,startpos,_), (_,endpos,_) -> (fn,startpos, endpos)
  
(*
  
   let firstspos_of_sposs xs =
     let rec first spos = function
       | []    -> spos
       | x::xs -> if spos=dummy_spos then first x xs else spos
     in 
     first dummy_spos xs

   let enclosedby posinside posoutside =
     not (startsbefore posinside posoutside) && not (endsbefore posoutside posinside)
  
   type positionedlabel = {labspos: sourcepos; lablab: Name.label}

   let string_of_positionedlabel poslab = 
     bracketed_string_of_pair string_of_sourcepos string_of_label (poslab.labspos, poslab.lablab)
*)

(* a service to the world ... *)
let warning pos string =
  flush stdout; 
  Printf.eprintf "\n** Warning! %s: %s **\n" (string_of_sourcepos pos) string;
  flush stderr

