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
(*  described in file LICENSE_LGL.                                        *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Based on traditional implementation of a binary heap using an array *)

module type Ordered = sig
  type t 
  val compare   : t -> t -> int
  (* val to_string : e -> string *)
end

exception Empty

module type PQ = sig

  (* A collection of [elt]s, ordered mostly by a random integer selected when
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

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit

  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  (* entries in queue order, not at all efficient *)
  val queue : t -> (int * elt) list
  
end

module Make(X : Ordered) = struct

  type elt = X.t (* int gives the ordering, mostly *)
  
  type oelt = int * elt (* the actual queue elements *)
  
  (* The heap is encoded in the array [data], where elements are stored
     from [0] to [size - 1]. From an element stored at [i], the left
     (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  type t = { mutable size : int; mutable data : oelt array }

  (* When [create n] is called, we cannot allocate the array, since there is
     no known value of type [elt]; we'll wait for the first addition to
     do it, and we remember this situation with a negative size. *)

  let create n =
    if n <= 0 then invalid_arg "create";
    { size = -n; data = [||] }

  let is_empty q = q.size <= 0

  (* [resize] doubles the size of [data] *)
  
  let compare (i,ei) (j,ej) =
    (* i and j rev-compared; otherwise X.compare *)
    let r = Pervasives.compare i j in
    if i=0 then X.compare ei ej else -r

  let resize q =
    let n = q.size in
    assert (n > 0);
    let n' = 2 * n in
    let d = q.data in
    let d' = Array.make n' d.(0) in
    Array.blit d 0 d' 0 n;
    q.data <- d'

  let push q x =
    let x = Random.bits (), x in
    (* first addition: we allocate the array *)
    if q.size < 0 then begin
      q.data <- Array.make (- q.size) x; q.size <- 0
    end;
    let n = q.size in
    (* resizing if needed *)
    if n == Array.length q.data then resize q;
    let d = q.data in
    (* moving [x] up in the heap *)
    let rec moveup i =
      let fi = (i - 1) / 2 in
      if i > 0 && compare d.(fi) x < 0 then begin
	d.(i) <- d.(fi);
	moveup fi
      end else
	d.(i) <- x
    in
    moveup n;
    q.size <- n + 1

  let first q =
    if q.size <= 0 then raise Empty;
    snd q.data.(0)

  let remove q =
    if q.size <= 0 then raise Empty;
    let n = q.size - 1 in
    q.size <- n;
    let d = q.data in
    let x = d.(n) in
    (* moving [x] down in the heap *)
    let rec movedown i =
      let j = 2 * i + 1 in
      if j < n then
	let j =
	  let j' = j + 1 in
	  if j' < n && compare d.(j') d.(j) > 0 then j' else j
	in
	if compare d.(j) x > 0 then begin
	  d.(i) <- d.(j);
	  movedown j
	end else
	  d.(i) <- x
      else
	d.(i) <- x
    in
    movedown 0

  (* this doesn't alter the ordering. It's based on Steve Cook's 'lust' 
     idea from Pascal-m, all those decades ago 
   *)
  let excite q = 
    let d = q.data in
    for i = 0 to q.size-1 do 
      let ix,e = d.(i) in
      d.(i) <- ix/2, e
    done

  let pop q = let m = first q in 
    remove q; 
    excite q;
    m

  let iter f q =
    let d = q.data in
    for i = 0 to q.size - 1 do f (snd d.(i)) done

  let fold f q x0 =
    let n = q.size in
    let d = q.data in
    let rec foldrec x i =
      if i >= n then x else foldrec (f (snd d.(i)) x) (succ i)
    in
    foldrec x0 0

  (* this is silly: sorting when we already have a heap. But it's only for diagnostic /
     display purposes, so it doesn't need to be efficient.
   *)
   
  let queue q =
    let n = q.size in
    let d = q.data in
    if n<=0 then []
    else 
      (let a = Array.make n d.(0) in
       Array.blit d 0 a 0 n;
       let r = Array.to_list a in
       List.sort compare r
      ) 
      
end
