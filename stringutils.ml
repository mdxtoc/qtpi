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

let commasep = String.concat ","

let is_empty s = s=""

let first s = s.[0]
let last s = s.[String.length s - 1]

let starts_with s prefix =
  try let pfx = String.sub s 0 (String.length prefix) in
      pfx=prefix
  with _ -> false
  
let ends_with s suffix =
  try let sfxlength = String.length suffix in
      let sfx = String.sub s (String.length s-sfxlength) sfxlength in
      sfx=suffix
  with _ -> false
  
let rec words s =
  if String.length s = 0 then []
  else
  if String.get s 0 = ' ' then words (String.sub s 1 (String.length s-1))
  else
    try let sidx = String.index s ' ' in
        String.sub s 0 sidx :: words (String.sub s (sidx+1) (String.length s-sidx-1))
    with Not_found -> [s]

let rec phrase = function
  | [s]     -> s
  | [s1;s2] -> s1 ^ " and " ^ s2
  | s :: ss -> s ^ ", " ^ phrase ss
  | []      -> "?none?"

let to_list s = Listutils.tabulate (String.length s) (fun i -> s.[i])
let of_list cs = String.init (List.length cs) (fun i -> List.nth cs i)