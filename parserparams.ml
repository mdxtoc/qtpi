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

let filename = ref ""			(* for creating sourcepos values *)

let offsideline = ref 0
let offsidelines = (ref [] : int list ref)

let curr_start = ref 0 (* set by Linesperson to the start offset of the token just read *)
let curr_end = ref 0   (* also set by Linesperson *)

let init_offside () =
  offsideline := 0;
  offsidelines := [];
  curr_start := 0;
  curr_end := 0

let offset_of_position position = position.Lexing.pos_cnum - position.Lexing.pos_bol

let is_offside () = !curr_start < !offsideline

type lr = Start | End

let push_offsideline lr = 
  offsidelines := !offsideline :: !offsidelines;
  offsideline := (match lr with Start -> !curr_start | End -> !curr_end)
  
let pop_offsideline () =
  match !offsidelines with
  | osl::osls -> offsideline := osl; offsidelines := osls
  | []        -> raise (Failure ("offside"))