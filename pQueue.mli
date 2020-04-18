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

module type OrderedPrio = sig
    type prio
    val compare : prio -> prio -> int (* pq is in descending order according to compare *)
end

module type Q = sig
  exception Empty

  type prio

  type 'a pq

  (* [create n] creates a new queue, with initial capacity [n] *)
  val create : int -> 'a pq

  (* [is_empty q] checks the emptiness of [q] *)
  val is_empty : 'a pq -> bool

  (* [push q (prio, x)] adds a new element [x] in queue [q]; size of [q] is doubled
     when maximum capacity is reached; complexity $O(log(n))$ *)
  val push : 'a pq -> prio -> 'a -> unit

  (* [first q] returns the first element of [q]; raises Empty
     when [q] is empty; complexity $O(1)$ *)
  val first : 'a pq -> 'a

  (* [remove q] removes the first element of [q]; raises Empty
     when [q] is empty; complexity $O(log(n))$ *)
  val remove : 'a pq -> unit

  (* [pop q] removes the first element of [q] and returns it;
     raises Empty when [q] is empty; complexity $O(log(n))$ *)
  val pop : 'a pq -> 'a

  (* [excite f q] alters the priority of each element of the queue from [p] to [f p]. 
     Requires that [f] doesn't alter the ordering. $O(n)$ *)
  val excite : (prio->prio) -> 'a pq -> unit

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : ('a -> unit) -> 'a pq -> unit

  val fold : ('a -> 'a -> 'a) -> 'a pq -> 'a -> 'a

  (* entries in queue order *)
  val to_list : 'a pq -> (prio * 'a) list
end

module Make (Ord: OrderedPrio) : Q with type prio = Ord.prio
  
