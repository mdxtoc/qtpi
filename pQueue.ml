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

exception Empty

(* A priority queue is a collection of elements, ordered by a random integer selected 
   when the element is added to the queue, smallest integer first. Each time an element is 
   taken from the queue, the integers of remaining elements are reduced, so their 
   'lust' to be chosen next increases a bit. So nobody, probably, gets overlooked 
   for ever.
   
   The 'lust' idea, and it's name, comes from Steve Cook who was working on Pascal-m
   at Queen Mary College in the 1980s. Hello Steve!
 *)

type 'a t = { mutable size : int; mutable data : (int * 'a) array }
  
  (* The heap is encoded in the array data, where elements are stored
     from [0] to [size - 1]. From an element stored at [i], the left
     (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

let leftchild i = 2*i+1 

let parent i = (i-1) / 2

let compare (i,ei) (j,ej) = (* all that matters is those integers ... *)
  - (Stdlib.compare i j)

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
    if i > 0 && compare d.(fi) x < 0 then 
      (d.(i) <- d.(fi);
       moveup fi
       ) 
     else
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

(* This is for diagnostic / display purposes, so it doesn't need to be efficient. *)
 
let elements q =
  let n = q.size in
  let d = q.data in
  if n<=0 then []
  else 
    (let d' = Array.copy d in
     let q = {size=n; data=d'} in
     let rec get els =
       try let el = pop q in
           get (el::els)
       with Empty -> List.rev els
     in
     get []
    ) 
      
(* this doesn't alter the ordering. It's based on Steve Cook's 'lust' 
   idea from Pascal-m, all those decades ago 
 *)
let excite q = 
  let d = q.data in
  for i = 0 to q.size-1 do 
    let ix,e = d.(i) in
    d.(i) <- ix/2, e
  done

