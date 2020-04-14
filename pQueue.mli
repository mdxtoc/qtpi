(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*
    This is Richard Bornat's modified version of Jean-Christophe Filliatre's 
    binary heap distribution v1.0.0, taken from 
    
    https://github.com/backtracking/bheap.git
    
*)

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

type 'a t

exception Empty

(* [create n] creates a new queue, with initial capacity [n] *)
val create : int -> 'a t

(* [is_empty q] checks the emptiness of [q] *)
val is_empty : 'a t -> bool

(* [push q x] adds a new element [x] in queue [q]; size of [q] is doubled
   when maximum capacity is reached; complexity $O(log(n))$ *)
val push : 'a t -> 'a -> unit

(* [first q] returns the first element of [q]; raises Empty
   when [q] is empty; complexity $O(1)$ *)
val first : 'a t -> 'a

(* [remove q] removes the first element of [q]; raises Empty
   when [q] is empty; complexity $O(log(n))$ *)
val remove : 'a t -> unit

(* [pop q] removes the first element of [q] and returns it;
   raises Empty when [q] is empty; complexity $O(log(n))$ *)
val pop : 'a t -> 'a

(* [excite q] reduces the random integer on each element of the queue. $O(n)$ *)
val excite : 'a t -> unit

(* usual iterators and combinators; elements are presented in
   arbitrary order *)
val iter : ('a -> unit) -> 'a t -> unit

val fold : ('a -> 'a -> 'a) -> 'a t -> 'a -> 'a

(* entries in queue order *)
val to_list : 'a t -> 'a list
