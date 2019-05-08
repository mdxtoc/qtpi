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
open Listutils
open Functionutils
open Basisv
open Number
open Name
open Process
open Pattern

exception Disaster of string

let vsize = Array.length
let msize = Array.length

let _for i inc n f = (* n is size, so up to n-1 *)
  let rec rf i =
    if i<n then (f i; rf (i+inc)) (* else skip *)
  in
  rf i
  
let _for_leftfold i inc n f v =
  let rec ff i v =
    if i<n then ff (i+inc) (f i v) else v
  in
  ff i v

let rec _for_rightfold i inc n f v =
  let rec ff i v =
    if i<n then f i (ff (i+inc) v) else v
  in
  ff i v

let _for_all i inc n f = 
  let rec ff i =
    if i<n then f i && ff (i+inc) else true
  in
  ff i 
  
let _for_exists i inc n f v = 
  let rec ff i =
    if i<n then f i || ff (i+inc) else false
  in
  ff i 
  
let queue_elements q = let vs = Queue.fold (fun vs v -> v::vs) [] q in
                       List.rev vs

let string_of_queue string_of sep q = 
  let vs = queue_elements q in
  "{" ^ string_of_list string_of sep vs ^ "}"

type value =
  | VUnit
  | VBit of bool
  | VNum of num
  | VBool of bool
  | VChar of char
  | VBasisv of basisv
  | VGate of gate
  | VString of string
  | VQbit of qbit
  | VQstate of string
  | VChan of chan
  | VTuple of value list
  | VList of value list
  | VFun of (value -> value)        (* with the environment baked in for closures *)
  | VProcess of name list * process

(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of h;
   i = sqrt -1; will be useful if we ever go complex. For now commented out.
   
   Note h^2=1/2; 
        f^2=h^2+h^3;
        g^2=h^2-h^3;
        fg = 1/2h = h^3  
 *)
and prob = 
  | P_0
  | P_1
  | P_f              
  | P_g 
  | P_h of int              
  | Psymb of qbit * bool    (* false=a, true=b, both random unknowns s.t. a**2+b**2 = 1 *)
  | Pneg of prob
  | Pprod of prob list      (* associative *)
  | Psum of prob list       (* associative *)

and cprob = C of prob*prob (* complex prob A + iB *)

and probvec = cprob array

and gate = cprob array array

and qbit = int

(* the gsum_info in channel waiter queues is to deal with guarded sums: an offer
   to communicate is withdrawn from all guards by setting the shared boolean to false.
   The channel list is to remove a space leak (blush): clear out the dead from those channels.
   The space leak is because we keep a set stuck_chans (a set?) for diagnostic printing purposes.
 *)
 
and chan = {cname: int; stream: value Queue.t; wwaiters: (wwaiter*gsum_info) PQueue.t; rwaiters: (rwaiter*gsum_info) PQueue.t}

and gsum_info = (bool * chan list) ref

and runner = name * process * env

and rwaiter = name * pattern * process * env

and wwaiter = name * value * process * env

and env = (name * value) list (* which, experiment suggests, is more efficient than Map at runtime *)

(* *********************** defining vectors, matrices ************************************ *)

let make_v = Array.of_list

let c_of_p p = C (p, P_0)

let c_0 = c_of_p P_0
let c_1 = c_of_p P_1
let c_h = c_of_p (P_h 1)
let c_f = c_of_p P_f
let c_g = c_of_p P_g

let c_i = C (P_0, P_1)

let pcneg  (C (x,y)) = (* only for local use, please *)
  let negate = function
    | P_0 -> P_0
    | p   -> Pneg p
  in
  C (negate x, negate y) 

let v_zero  = make_v [c_1   ; c_0         ]
let v_one   = make_v [c_0   ; c_1         ]
let v_plus  = make_v [c_h   ; c_h         ]
let v_minus = make_v [c_h   ; pcneg c_h   ]

let v_1 = make_v [c_1] (* a unit for folding *)
let v_0 = make_v [c_0] (* another unit for folding *)

let make_m rows = rows |> (List.map Array.of_list) |> (Array.of_list)

let m_I  = make_m   [[c_1       ; c_0        ];
                     [c_0       ; c_1        ]] 
let m_X  = make_m   [[c_0       ; c_1        ];
                     [c_1       ; c_0        ]] 
let m_Y  = make_m   [[c_0       ; pcneg c_i  ];
                     [c_i       ; c_0        ]]
let m_Z  = make_m   [[c_1       ; c_0        ];
                     [c_0       ; pcneg c_1  ]] 
let m_H  = make_m   [[c_h       ; c_h        ];
                     [c_h       ; pcneg (c_h)]]
                     
(* these two are intended to be like rotations. Unlike H, F*F<>I *)

let m_F  = make_m   [[c_f       ; pcneg c_g  ];
                     [c_g       ; c_f        ]]
let m_G  = make_m   [[c_g       ; pcneg c_f  ];
                     [c_f       ; c_g        ]]

let m_Phi = function (* as Pauli *)
  | 0 -> m_I
  | 1 -> m_X
  | 2 -> m_Y  
  | 3 -> m_Z  
  | i -> raise (Disaster ("** _Phi(" ^ string_of_int i ^ ")"))

let m_Cnot = make_m  [[c_1; c_0; c_0; c_0];
                      [c_0; c_1; c_0; c_0];
                      [c_0; c_0; c_0; c_1];
                      [c_0; c_0; c_1; c_0]]
                     
let m_1 = make_m [[c_1]] (* a unit for folding *)
let m_0 = make_m [[c_0]] (* another unit for folding *)

(* string_of_ functions *)
let string_of_pqueue stringof sep pq = 
  "{" ^ string_of_list stringof sep (PQueue.elements pq) ^ "}"
;;

(* so_value takes an argument optf to winnow out those things we don't want it to deal with directly *)
(* this is to allow the library function 'show' to work properly. The rest of the world can use string_of_value *)
let rec so_value optf v =
  match optf v with
  | Some s -> s
  | None   -> (match v with
               | VUnit           -> "()"
               | VBit b          -> if b then "1" else "0"
               | VNum n          -> string_of_num n
               | VBool b         -> string_of_bool b
               | VBasisv bv      -> string_of_basisv bv
               | VGate gate      -> string_of_gate gate
               | VChar c         -> Printf.sprintf "'%s'" (Char.escaped c)
               | VString s       -> Printf.sprintf "\"%s\"" (String.escaped s)
               | VQbit q         -> "Qbit " ^ string_of_qbit q
               | VQstate s       -> s
               | VChan c         -> "Chan " ^ so_chan optf c
               | VTuple vs       -> "(" ^ string_of_list (so_value optf) "," vs ^ ")"
               | VList vs        -> bracketed_string_of_list (so_value optf) vs
               | VFun f          -> "<function>"
               | VProcess (ns,p) -> Printf.sprintf "process (%s) %s"
                                                   (string_of_list string_of_name "," ns)
                                                   (string_of_process p)
              )
and short_so_value optf v =
  match optf v with
  | Some s -> s
  | None   -> (match v with
               | VQbit q         -> "Qbit " ^ short_string_of_qbit q
               | VChan c         -> "Chan " ^ short_so_chan optf c
               | VTuple vs       -> "(" ^ string_of_list (short_so_value optf) "," vs ^ ")"
               | VList vs        -> bracketed_string_of_list (short_so_value optf) vs
               | VProcess (ns,p) -> Printf.sprintf "process (%s)"
                                                   (string_of_list string_of_name "," ns)
               | v               -> so_value optf v
              )
  
and so_chan optf {cname=i; stream=vs; rwaiters=rq; wwaiters=wq} =
    Printf.sprintf "%d = vs:{%s} rs:{%s} ws:{%s}"
                   i
                   (string_of_queue (so_value optf) "; " vs)
                   (string_of_pqueue (short_so_rwaiter optf) "; " rq)
                   (string_of_pqueue (short_so_wwaiter optf) "; " wq)

and short_so_chan optf {cname=i} =
    string_of_int i
    
and so_env optf env =
  "{" ^ string_of_assoc string_of_name (so_value optf) ":" ";" env ^ "}"

and short_so_env optf env =
  "{" ^  string_of_assoc string_of_name (short_so_value optf)  ":" ";" 
                         (List.filter (function 
                                       | _, VFun     _ 
                                       | _, VProcess _ -> false
                                       | _             -> true
                                      )
                                      env 
                         ) ^
  "}"   
  
and so_runner optf (n, proc, env) =
  Printf.sprintf "%s = (%s) %s" 
                 (string_of_name n)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 
and so_rwaiter optf ((n, pat, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_rwaiter optf ((n, pat, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (string_of_pattern pat)
                 (if fst !gsir then "" else "[dead]")
                 
and so_wwaiter optf ((n, v, proc, env),gsir) = 
  Printf.sprintf "%s = (%s)%s %s%s" 
                 (string_of_name n)
                 (so_value optf v)
                 (short_string_of_process proc)
                 (short_so_env optf env)
                 (if fst !gsir then "" else "[dead]")
                 
and short_so_wwaiter optf ((n, v, proc, env),gsir) = (* infinite loop if we print the environment *)
  Printf.sprintf "%s(%s)%s" 
                 (string_of_name n)
                 (so_value optf v)
                 (if fst !gsir then "" else "[dead]")
                 
and so_runnerqueue optf sep rq =
  string_of_pqueue (so_runner optf) sep rq

and string_of_qbit = string_of_int

and short_string_of_qbit = string_of_int

and string_of_prob p = 
  (* Everything is associative, but the normal form is sum of negated products.
   * So possbra below puts in _very_ visible brackets, for diagnostic purposes.
   *)
  let prio = function
    | P_0
    | P_1
    | P_f  
    | P_g 
    | P_h  _ 
    | Psymb _         -> 10
    | Pprod _         -> 8
    | Pneg  _         -> 6
    | Psum  _         -> 4
  in
  let possbra p' = 
    let supprio = prio p in
    let subprio = prio p' in
    let s = string_of_prob p' in
    if subprio<=supprio then "!!(" ^ s ^ ")!!" else s
  in
  match p with
  | P_0             -> "0"
  | P_1             -> "1"
  | P_f             -> "f"
  | P_g             -> "g"
  | P_h 1           -> "h"
  | P_h n           -> Printf.sprintf "h(%d)" n
  | Psymb (q,b)     -> Printf.sprintf "%s%s" (if b then "b" else "a") (string_of_qbit q)
  | Pneg p'         -> "-" ^ possbra p'
  | Pprod ps        -> String.concat "*" (List.map possbra ps)
  | Psum  ps        -> sum_separate (List.map possbra ps)    

and sum_separate = function
 | p1::p2::ps -> if Stringutils.starts_with p2 "-" then p1 ^ sum_separate (p2::ps) 
                 else p1 ^ "+" ^ sum_separate (p2::ps) 
 | [p]        -> p
 | []         -> raise (Can'tHappen "sum_separate []")

and string_of_cprob (C (x,y)) =
  let im y = 
    match y with
    | P_1     -> "i"
    | P_f  
    | P_g 
    | P_h   _ 
    | Psymb _ 
    | Pprod _ -> "i*" ^ string_of_prob y
    | _       -> "i*(" ^ string_of_prob y ^ ")"
  in
  match x,y with
  | P_0, P_0    -> "0"
  | _  , P_0    -> string_of_prob x
  | P_0, Pneg p -> "-" ^ im p
  | P_0, _      -> im y
  | _  , Pneg p -> string_of_prob x ^ "-" ^ im p
  | _  , _      -> string_of_prob x ^ "+" ^ im y
  
and string_of_probvec v =
  if !Settings.fancyvec then 
    (let n = vsize v in
     let rec ln2 n r = if n=1 then r
                       else ln2 (n lsr 1) (r+1)
     in
     let width = ln2 n 0 in
     let string_of_bin i =
       let rec sb i k =
         if k=width then ""
         else sb (i/2) (k+1) ^ (if i mod 2 = 0 then "0" else "1")
       in
       sb i 0
     in
     let string_of_basis_idx i =
       Printf.sprintf "|%s>" (string_of_bin i)
     in
     let estrings = _for_leftfold 0 1 n
                      (fun i ss -> match string_of_cprob v.(i) with
                                   | "0"  -> ss
                                   | "1"  -> (string_of_basis_idx i) :: ss
                                   | "-1" -> ("-" ^ string_of_basis_idx i) :: ss
                                   | s   ->  (Printf.sprintf "%s%s" 
                                                             s 
                                                             (string_of_basis_idx i)
                                             ) :: ss
                      )
                      []
     in
     match estrings with
     | []  -> "??empty probvec??"
     | [e] -> e
     | _   -> Printf.sprintf "(%s)" (sum_separate (List.rev estrings))
    )
  else
    (let estrings = Array.fold_right (fun p ss -> string_of_cprob p::ss) v [] in
     Printf.sprintf "(%s)" (String.concat " <,> " estrings)
    )
  
and string_of_matrix m =
  let strings_of_row r = Array.fold_right (fun p ss -> string_of_cprob p::ss) r [] in
  let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
  let rwidth r = List.fold_left max 0 (List.map String.length r) in
  let width = List.fold_left max 0 (List.map rwidth block) in
  let pad s = s ^ String.make (width - String.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}" block
  
and string_of_gate g = 
  if !Settings.showsymbolicgate then
    (if g=m_I then "I" else
     if g=m_X then "X" else
     if g=m_Y then "Y" else
     if g=m_Z then "Z" else
     if g=m_H then "H" else
     if g=m_F then "F" else
     if g=m_G then "G" else
     if g=m_Cnot then "Cnot" else
     string_of_matrix g
    )
  else string_of_matrix g

(* ********************************************************************************************************** *)

let doptf s = None

let string_of_value = so_value doptf
let short_string_of_value = short_so_value doptf 

let string_of_env = so_env doptf
let short_string_of_env = short_so_env doptf 

let string_of_chan = so_chan doptf
let short_string_of_chan = short_so_chan doptf 

let string_of_runnerqueue = so_runnerqueue doptf

