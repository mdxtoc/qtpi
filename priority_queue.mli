(*
    This is Richard Bornat's modified version of Jean-Christophe Filliatre's 
    binary heap distribution v1.0.0, taken from 
    
    https://github.com/backtracking/bheap.git
    
    His copyright is stated below.
*)
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

module type Ordered = sig
  type t (* and no compare function: not needed *)
end

exception Empty

module type PQ = sig

  (* A collection of [elt]s, ordered by a random integer selected when
     the [elt] is added to the queue, smallest integer first. Each time an [elt] is 
     taken from the queue, the integers of remaining elements are reduced, so their 
     'lust' to be chosen next increases a bit. So nobody, probably, gets overlooked 
     for ever.
   *)

  type t
  
  type elt 

  (* [create n] creates a new queue, with initial capacity [n] *)
  val create : int -> t

  (* [is_empty q] checks the emptiness of [q] *)
  val is_empty : t -> bool

  (* [push q x] adds a new element [x] in queue [q]; size of [q] is doubled
     when maximum capacity is reached; complexity $O(log(n))$ *)
  val push : t -> elt -> unit

  (* [first q] returns the first element of [q]; raises [EmptyHeap]
     when [q] is empty; complexity $O(1)$ *)
  val first : t -> elt

  (* [remove q] removes the first element of [q]; raises [EmptyHeap]
     when [q] is empty; complexity $O(log(n))$ *)
  val remove : t -> unit

  (* [pop q] removes the first element of [q] and returns it;
     raises [EmptyHeap] when [q] is empty; complexity $O(log(n))$ *)
  val pop : t -> elt

  (* [excite q] reduces the random integer on each element of the queue. $O(n)$ *)
  val excite : t -> unit

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit

  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  (* entries in queue order, not at all efficient *)
  val queue : t -> (int * elt) list

  (* the compare function the module uses: useful for sorting the results of queue above *)
  val compare : (int*elt) -> (int*elt) -> int
end

module Make(Ord: Ordered) : PQ with type elt = Ord.t