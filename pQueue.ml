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

(* Based on traditional implementation of a binary heap using an array *)

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

module Make (Ord : OrderedPrio) = struct
  exception Empty

  type prio = Ord.prio
  
  (* A priority queue is a collection of elements, ordered by a priority selected 
     when the element is added to the queue. 
   *)

  type 'a pq = { mutable size : int; mutable data : (prio * 'a) array }
  
    (* The heap is encoded in the array data, where elements are stored
       from [0] to [size - 1]. From an element stored at [i], the left
       (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  let leftchild i = 2*i+1 

  let parent i = (i-1) / 2

  let compare (i,_) (j,_) = Ord.compare i j

  (* When [create n] is called, we cannot allocate the array, since there is
     no known value of type element; we'll wait for the first addition to
     do it, and we remember this situation with a negative size. *)

  let create n =
    if n <= 0 then invalid_arg "create";
    { size = -n; data = [||] }

  let is_empty q = q.size <= 0

  (* [resize] doubles the size of data *)

  let resize q =
    let n = q.size in
    assert (n > 0);
    let n' = 2 * n in
    let d = q.data in
    let d' = Array.make n' d.(0) in
    Array.blit d 0 d' 0 n;
    q.data <- d'

  let push q prio x =
    let x = prio, x in
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
      if i > 0 && compare d.(fi) x < 0 then 
        (d.(i) <- d.(fi);
         moveup fi
         ) 
       else
         d.(i) <- x
    in
    moveup n;
    q.size <- n + 1

  let firstpair q = 
    if q.size <= 0 then raise Empty;
    q.data.(0)

  let first q = snd (firstpair q)
  
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
        if compare d.(j) x > 0 then 
           ( d.(i) <- d.(j);
            movedown j
           ) 
         else
          d.(i) <- x
     else
       d.(i) <- x
    in
    movedown 0

  let pop q = let m = first q in 
    remove q; 
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
 
  let to_list q =
    let n = q.size in
    let d = q.data in
    if n<=0 then []
    else 
      (let d' = Array.copy d in
       let q = {size=n; data=d'} in
       let rec get els =
         try let el = firstpair q in
             remove q;
             get (el::els)
         with Empty -> List.rev els
       in
       get []
      ) 
      
  (* Each time an element is taken from the queue, the priorities of remaining elements are increased, 
     so their 'lust' to be chosen next increases a bit. So nobody, probably, gets overlooked 
     for ever.
   
     The 'lust' idea, and its name, comes from Steve Cook who was working on Pascal-m with me
     at Queen Mary College in the 1980s. Hello Steve!
     
     [excite f q] requires that [f] doesn't alter the ordering. 
   *)
  let excite f q = 
    let d = q.data in
    for i = 0 to q.size-1 do 
      let ix,e = d.(i) in
      d.(i) <- f ix, e
    done
end
