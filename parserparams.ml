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

let offsideline = ref 0
let offsidelines = (ref [] : int list ref)

let curr_start = ref 0 (* set by Linesperson to the start offset of the token just read *)
let curr_end = ref 0   (* also set by Linesperson *)
let curr_offside = ref false (* Linesperson again *)

let init_offside () =
  offsideline := 0;
  offsidelines := [];
  curr_start := 0;
  curr_end := 0

let offset_of_position position = position.Lexing.pos_cnum - position.Lexing.pos_bol

let is_offside () = !curr_start < !offsideline

type lr = Prev | Here | Next

let push_pending = ref 0

let do_push_offsideline offset = 
  if !verbose_offside then
    Printf.eprintf "do_push_offsideline %d\n" offset;
  (* we do not set an offside position! *)
  offsidelines := !offsideline :: !offsidelines;
  if offset >= !offsideline then offsideline := offset
  
let push_offsideline = function
  | Prev    -> if !verbose_offside then
                 Printf.eprintf "push_offsideline Prev %d\n" !curr_start;
               do_push_offsideline !curr_start
  | Here    -> if !verbose_offside then
                 Printf.eprintf "push_offsideline Here %d\n" !curr_end;
               do_push_offsideline !curr_end (* oh I wish it could be !curr_end + 1 *)
  | Next    -> if !verbose_offside then
                 Printf.eprintf "push_offsideline Next %d\n" !push_pending;
               push_pending := !push_pending+1
  
let pop_offsideline () =
  match !offsidelines with
  | osl::osls -> if !verbose_offside then
                   Printf.eprintf "pop_offsideline %d\n" osl;
                 offsideline := osl; offsidelines := osls
  | []        -> raise (Failure ("offside"))
  