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
open Optionutils
open Tupleutils
open Snum
open Forutils
open Number

exception Error of string
exception Disaster of string

let my_to_int n s =
  try Z.to_int n with Z.Overflow -> raise (Disaster (Printf.sprintf "to_int %s in %s" (string_of_zint n) s))
  
(* find log_2 n, but only if n is a power of 2 -- else raise Invalid_argument *)
let log_2 n :zint =
  Z.(let rec find_twopower r i =
       if i=one                   then r                                                      else
       if i=one || i land one=one then raise (Invalid_argument ("log_2 " ^ string_of_zint n)) else
                                       find_twopower (r+one) (i asr 1)
       in
       find_twopower zero n
    )

(* *********************** vectors, matrices,gates ************************************ *)

(* because matrices and vectors can become very large (see the W example), indices are now zint *)
(* because Arrays can't get that large, they are indexed by ints. Ho hum. *)

type dvec  = csnum array
and  cvec  = (zint * csnum) list                 (* assoc list *)

type vector = 
  | DenseV   of dvec                            (* always 2^n-sized, but we don't have existential type for that *)
  | SparseV  of zint * csnum * cvec             (* size, default value, values *)

and matrix = 
  | DenseM of dmat                              (* not necessarily square *)
  | SparseM of zint * csnum * cvec array        (* csize, default value, sparse rows *)
  | FuncM  of string * zint * zint * (zint -> zint -> csnum) * (csnum * (zint -> cvec) * (zint -> cvec)) option
                                                (* rsize, csize, element function, sparse row/column option *)

and dmat = csnum array array

and nv = modulus * vector                       (* modulus, vector: meaning 1/sqrt(modulus)(vec) *)

and modulus = snum 

and gate = matrix                               (* gates must be square, unitary and 2^n-sized, 
                                                   but to say that we would need an existential type.
                                                 *)

let string_of_cv assoc = Printf.sprintf "[%s]" (string_of_assoc string_of_zint string_of_csnum ":" ";" assoc)

let vsize = function
  | DenseV  v       -> Z.of_int (Array.length v)
  | SparseV (n,_,_) -> n

let nvsize (_,v) = vsize v
        
let rsize = function
  | DenseM m                -> Z.of_int (Array.length m)
  | SparseM (nc, sv, cvs)   -> Z.of_int (Array.length cvs)
  | FuncM  (_,nr,_,_,_)     -> nr

let csize = function
  | DenseM m                -> if Array.length m = 0 then z_0 else Z.of_int (Array.length m.(0))
  | SparseM (nc, sv, cvs)   -> nc
  | FuncM  (_,_,nc,_,_)     -> nc

let gsize = rsize

(* cvecs are ordered ... *)

let cvseg n m cv = (* n<=i<m, natch *)
  takewhile (fun (i,_) -> i<:m) (dropwhile (fun (i,_) -> i<:n) cv)
  
let rec find_cv sv xs i =
  match xs with
  | (j,x)::xs -> if i<:j then sv else if i=:j then x else find_cv sv xs i
  | []        -> sv

(* accessing vectors whatever the form *)
let (?.) v i = 
  match v with 
  | DenseV  v           -> v.(Z.to_int i)
  | SparseV (_, sv, cv) -> find_cv sv cv i

(* accessing matrices whatever the form *)
let (?..) m i j =
  match m with
  | DenseM m                -> m.(Z.to_int i).(Z.to_int j)
  | SparseM (_,sv,cvv)      -> find_cv sv (cvv.(Z.to_int i)) j
  | FuncM  (_,_,_,f,_)      -> f i j

(* a bit of false recursion, so I don't have to find what order to put these functions in 
   -- all so I can use string_of_vector in diag printing when I need to
 *)
type bksign = PVBra | PVKet

let rec densify_cv n sv cv = Array.init (my_to_int n "densify_cv") (find_cv sv cv <.> Z.of_int)

and densify_v =
  function
  | DenseV v          -> v
  | SparseV (n,sv,cv) -> densify_cv n sv cv
  
and dense_countzeros_v n m v :int = (* from n to m-1, natch *)
  _for_fold_left n 1 m 0 (fun nzs i -> if v.(i)=c_0 then nzs+1 else nzs)
  
and countzeros_v n m v :zint = (* from n to m-1, natch *)
  if n>=:m then z_0 else match v with
                      | DenseV  v                     -> Z.of_int (dense_countzeros_v (Z.to_int n) (Z.to_int m) v)
                      | SparseV (_,sv,cv) when sv=c_0 -> let cv' = cvseg n m cv in Z.(m-n-Z.of_int (List.length cv'))
                      | SparseV (nc,sv,cv)            -> 
                          Z.(List.fold_left (fun nz (_,x) -> if x=c_0 then nz+z_1 else nz) z_0 cv)

and cv_of_dv sv dv = 
  let nxs = Array.to_list (Array.mapi (fun i x -> (Z.of_int i),x) dv) in
  List.filter (fun (_,x) -> x<>sv) nxs

and svfreq_v v =
  let stats = statistics_v v in List.hd stats
  
and maybe_sparse_v dv =
  let v = DenseV dv in
  if vsize v>:z_4 then
     (let sv,freq = svfreq_v v in
      let n = Z.of_int (Array.length dv) in
      if Z.(freq*z_4>z_3*n) then SparseV (n, sv, cv_of_dv sv dv)
                            else v
    )
  else v

and dv_of_cv sv (n:zint) cv =
  let dv = Array.make (my_to_int n "dv_of_cv 1") sv in
  List.iter (fun (i,x) -> dv.(my_to_int i "dv_of_cv 2") <- x) cv;
  dv

and maybe_dense_v sv n cv =
  let dense () = DenseV (dv_of_cv sv n cv) in
  if n>:z_4 then
    (let vv = SparseV (n, sv, cv) in
     let stats = statistics_v vv in
     let sv',freq = List.hd stats in
     if Z.(freq*z_4>z_3*n) then
       if sv=sv' then vv 
                 else SparseV (n,sv',sparse_elements_cv sv sv' n cv) (* should this be DenseV?? *)
     else dense()
    )
  else dense()

and sparse_elements_cv sv sv' n cv = (* fill in all the gaps with sv, cut out all the sv's *)
  if sv=sv' then cv else
    (let rec svs k n ixs =
       if k=:n then ixs else svs (k+:z_1) n ((k,sv)::ixs) 
     in
     let rec f ixs k = function
       | []        -> List.rev (svs k n ixs)
       | (i,x)::cv -> let ixs = svs k i ixs in
                      f (if x=sv' then ixs else (i,x)::ixs) (i+:z_1) cv
     in 
     f [] z_0 cv
    )
                   
and sparse_elements_dv sv dv = List.filter (fun (_,x) -> x<>sv) (Array.to_list (Array.mapi (fun i x -> Z.of_int i,x) dv))

and sparse_elements_v sv vV =
  match vV with
  | SparseV (n,sv',cv) -> if sv=sv' then cv 
                          else sparse_elements_cv sv sv' n cv
  | DenseV  v          -> sparse_elements_dv sv v

and vseg n m v = (* from n to m-1, natch *)
  match v with
  | DenseV  dv          -> DenseV (Array.init (Z.to_int (m-:n)) (fun i -> dv.(Z.to_int n+i)))
  | SparseV (_, sv, cv) -> SparseV (m-:n, sv, List.map (fun (i,x) -> i-:n,x) (cvseg n m cv))

(* zeroseg is commented out. This code compiles, and would probably work, but 
   zeroseging a sparse array is a silly idea. It was only used in qmeasure, and 
   vseg is a much better idea.
   
   and zeroseg n m v = (* from n to m-1, natch *) 
     match v with
     | DenseV  dv          -> 
         let dv' = Array.copy dv in
         for i = Z.to_int n to Z.to_int m-1 do dv'.(i) <- c_0 done;
         DenseV dv'
     | SparseV (k, sv, cv) -> 
         let pre, post = cvseg z_0 n cv, cvseg m k cv in
         if sv=c_0 then SparseV (k, sv, pre@post)
         else (* either sv or c_0 is the new most-frequent value *)
           (let sev = sparse_elements_cv in
            (* if the empty seg is half of the original then almost certainly it will be c_0, otherwise probably sv *)
            if Z.((m-n)*z_2>=k) then maybe_dense_v c_0 k (sev sv c_0 n pre @ sev sv c_0 (k-:m) post)
                              else maybe_dense_v sv k (pre @ sev c_0 sv (m-:n) [] @ post)
           )
 *)
 
and map_v f = function
  | SparseV (n, sv, cv) -> SparseV (n, f sv, List.map (fun (i,x) -> i, f x) cv)
  | DenseV  dv          -> maybe_sparse_v (Array.map f dv)

(* and intersect_cv cvA cvB =
     let rec inter rs cvA cvB =
       match cvA, cvB with
       | (i,x)::ixs, (j,y)::jys -> if i<j then inter rs            ixs cvB else
                                   if i=j then inter ((i,(x,y))::rs) ixs jys else
                                               inter rs            cvA jys
       | _                      -> List.rev rs
     in
     inter [] cvA cvB
  
   and union_cv cvA cvB =
     let rec union rs cvA cvB =
       match cvA, cvB with
       | (i,x)::ixs, (j,y)::jys -> if i<j then union ((i,(x  ,c_0))::rs) ixs cvB else
                                   if i=j then union ((i,(x  ,y  ))::rs) ixs jys else
                                               union ((j,(c_0,y  ))::rs) cvA jys
       | _                      -> List.rev rs
     in
     union [] cvA cvB
 *)
 
and string_of_nv bksign = 
  let so_v v =
    if !Settings.fancyvec then 
      (let n = vsize v in
       let width = log_2 n in
       let string_of_bin i =
         let rec sb i k =
           if k=:width then ""
           else sb Z.(i/z_2) Z.(k+z_1) ^ (if Z.(i mod z_2 = z_0) then "0" else "1")
         in
         sb i z_0
       in
       let string_of_basis_idx i =
         Printf.sprintf (match bksign with PVBra -> "<%s|" | PVKet -> "|%s>") (string_of_bin i)
       in
       let mustbracket (C(real,im)) = 
         (* all but simple real sums are bracketed in string_of_csnum *)
         match real, im with
         | S_sum _, S_0 -> true
         | _            -> false
       in
       let estringf ss (i,x) = match string_of_csnum x with
                           | "0"  -> ss
                           | "1"  -> (string_of_basis_idx i) :: ss
                           | "-1" -> ("-" ^ string_of_basis_idx i) :: ss
                           | s   ->  (Printf.sprintf "%s%s" 
                                                     (if mustbracket x then "(" ^s ^ ")" else s) 
                                                     (string_of_basis_idx i)
                                     ) :: ss
       in
       let estrings = match v with
                      | SparseV (_, sv, cv) 
                          when sv=c_0       -> List.fold_left estringf [] cv 
                      | _                   -> _for_fold_leftZ z_0 z_1 n [] (fun ss i -> estringf ss (i,?.v i))
       in
       match estrings with
       | []  -> "?..empty nv?.."
       | [e] -> e
       | _   -> Printf.sprintf "(%s)" (sum_separate (List.rev estrings))
      )
    else
      match v with
      | DenseV  v         -> let estrings = Array.fold_right (fun s ss -> string_of_csnum s::ss) v [] in
                             Printf.sprintf "DenseV⟨%s⟩" (String.concat "," estrings)
      | SparseV (n,sv,cv) -> Printf.sprintf "SparseV(%s,%s[%s])" (string_of_zint n) (string_of_csnum sv) (string_of_cv cv)
  in
  let normalised_sign vv = 
    let doit x = 
      match (string_of_csnum x).[0] with
      | '-' -> so_v (map_v cneg vv)
      | _   -> so_v vv 
    in
    match vv with
    | SparseV (_, sv, (i,x)::_) -> if sv=c_0 || i=z_0 then doit x else doit sv
    | SparseV (n, sv, []      ) -> doit sv
    | DenseV  v                 -> let xs = dropwhile ((=) c_0) (Array.to_list v) in
                                   match xs with
                                   | x::xs -> doit x
                                   | []    -> so_v vv
  in
  function
  | S_h 0, vv -> normalised_sign vv
  | vm , vv -> Printf.sprintf "<<%s>>%s" (string_of_snum vm) (normalised_sign vv)
  
and string_of_bra b = string_of_nv PVBra b
and string_of_ket k = string_of_nv PVKet k

and string_of_vector v = string_of_ket (S_h 0,v)

(* with sparse vectors, we can have some seriously large ones ... *)
and statistics_v v :(csnum*zint) list =
  let stats = CsnumHash.create 1000 in
  let get cn = try CsnumHash.find stats cn with _ -> (let r = ref z_0 in CsnumHash.add stats cn r; r) in
  let count cn = let r = get cn in r:=!r+:z_1 in
  (match v with
   | DenseV  dv        -> Array.iter count dv
   | SparseV (n,sv,cv) -> let r = get sv in
                          r:=!r+:(n-:Z.of_int (List.length cv));
                          List.iter (fun (_,x) -> count x) cv
  );
  let compare (i,fi) (j,fj) = ~-(Z.compare fi fj) in
  List.sort compare (List.map (fun (v,r) -> v,!r) (CsnumHash.to_assoc stats))

let statistics_nv (_,v) = statistics_v v

let string_of_matrix = function
  | DenseM m -> 
      let strings_of_row r = Array.fold_right (fun s ss -> string_of_csnum s::ss) r [] in
      let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
      let rwidth r = List.fold_left max 0 (List.map String.length r) in
      let width = List.fold_left max 0 (List.map rwidth block) in
      let pad s = s ^ String.make (width - String.length s) ' ' in
      let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
      Printf.sprintf "\n{%s}\n" block
  | SparseM (nc,sv,cvv) ->   
      Printf.sprintf "SparseM %s %s ⟨%s⟩\n" (string_of_zint nc) (string_of_csnum sv) (string_of_list string_of_cv ";" (Array.to_list cvv))
  | FuncM (id,nr,nc,_,opt) ->
      Printf.sprintf "FuncM(%s,%s,%s,_,%s)" id (string_of_zint nr) (string_of_zint nc) (Optionutils.string_of_option (fun _ -> "_,_") opt)
      
let string_of_gate = string_of_matrix

let statistics_m m :(csnum*zint) list =
  let stats = CsnumHash.create 1000 in
  let get cn = try CsnumHash.find stats cn with _ -> (let r = ref z_0 in CsnumHash.add stats cn r; r) in
  let count cn = let r = get cn in r:=!r+:z_1 in
  (match m with
   | DenseM  dm          -> Array.iter (Array.iter count) dm
   | SparseM (nc,sv,cvv) -> let svr = get sv in
                            let count_cv cv = 
                              svr:=!svr+:(nc-:Z.of_int (List.length cv));
                              List.iter (count <.> snd) cv
                            in
                            Array.iter count_cv cvv
   | FuncM (_,nr,nc,f,_) -> _forZ z_0 z_1 nr (fun i ->
                              _forZ z_0 z_1 nc (fun j -> count (f i j))
                            )
  );
  let compare (i,fi) (j,fj) = ~-(Z.compare fi fj) in
  List.sort compare (List.map (fun (v,r) -> v,!r) (CsnumHash.to_assoc stats))

let countzeros_dm dm :int = 
  Array.fold_left (Array.fold_left (fun n x -> if x=c_0 then n+1 else n)) 0 dm

let cvv_of_dm sv = Array.map (cv_of_dv sv)

let svfreq_m m =  
  let stats = statistics_m m in
  List.hd stats

let maybe_sparse_m dm =
  let m = DenseM dm in
  if rsize m>:z_4 then
    (let sv,freq = svfreq_m m in
     let nr, nc = rsize m, csize m in
     if Z.(freq*z_4 > z_3*nr*nc) then SparseM (nc, sv, cvv_of_dm sv dm)
                                 else m
    )
  else m

let dm_of_cvv sv nc cvv = Array.map (dv_of_cv sv nc) cvv

let maybe_dense_m sv nc cvv = 
  let dense() = DenseM (dm_of_cvv sv nc cvv) in
  if nc>:z_4 then
    (let m = SparseM (nc, sv, cvv) in
     let sv',freq = svfreq_m m in
     let nr = rsize m in
     if Z.(freq*z_4 > z_3*nr*nc) then 
       if sv=sv' then m
                 else SparseM (nc, sv', Array.map (sparse_elements_cv sv sv' nc) cvv)
     else dense()
    )
  else dense()
  
module OrderedPrioZ = struct type prio = zint
                            let compare = (~-)<..>Z.compare
                     end

module Zpq = PQueue.Make (OrderedPrioZ)

module CvvH = struct type t = cvec array 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = bracketed_string_of_list string_of_cv <.> Array.to_list
               end
module CvvHash = MyHash.Make (CvvH)

let cvvtab = CvvHash.create (100)

let transpose_cvv cvv =
  try CvvHash.find cvvtab cvv
  with _ -> 
      let rvv = Array.map (fun cv -> Zpq.create (List.length cv+1)) cvv in
      Array.iteri (fun i cv -> List.iter (fun (j,x) -> Zpq.push rvv.(my_to_int j "transpose_cvv") (Z.of_int i) x) cv) cvv;
      let r = Array.map Zpq.to_list rvv in
      CvvHash.add cvvtab cvv r;
      r
  
module DmatH = struct type t = dmat 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = (fun dm -> string_of_matrix (DenseM dm))
               end
module DMatHash = MyHash.Make (DmatH)
                    
let rcftab = DMatHash.create (100)

let rowfopt_m = function
  | SparseM (n, sv, cvv)      -> Some (sv, Array.get cvv <.> Z.to_int, Array.get (transpose_cvv cvv) <.> Z.to_int)
  | FuncM   (id,nr,nc,f,optf) -> optf
  | DenseM dm as m            -> (* if we are asked, it's needed *)
                                 try Some (DMatHash.find rcftab dm) 
                                 with Not_found -> let sv,_ = svfreq_m m in
                                                   let cvv = cvv_of_dm sv dm in
                                                   let r = sv, Array.get cvv <.> Z.to_int, Array.get (transpose_cvv cvv) <.> Z.to_int in
                                                   DMatHash.add rcftab dm r;
                                                   Some r
                       
(* ********************** build vectors, matrices, gates ******************************* *)

let minus  (C (x,y)) = (* only for local use, please *)
  let negate = function
    | S_0 -> S_0
    | s   -> S_neg s
  in
  C (negate x, negate y) 

let make_nv ss = S_h 0, DenseV (Array.of_list ss)

let nv_zero  = make_nv [c_1   ; c_0         ]
let nv_one   = make_nv [c_0   ; c_1         ]
let nv_plus  = make_nv [c_h   ; c_h         ]
let nv_minus = make_nv [c_h   ; minus c_h   ]

let nv_1 = make_nv [c_1] (* a unit for folding *)
let nv_0 = make_nv [c_0] (* another unit for folding *)

let make_m rows = maybe_sparse_m (rows |> (List.map Array.of_list) |> (Array.of_list))

let matrix_of_gate g = g    (* trivial now *)

(* this should only be used if it's really a unitary matrix *)               
let gate_of_matrix m = m
  
let make_g rows = 
  gate_of_matrix (make_m rows)

let g_I  = make_g   [[c_1       ; c_0        ];
                     [c_0       ; c_1        ]] 
let g_X  = make_g   [[c_0       ; c_1        ];
                     [c_1       ; c_0        ]] 
let g_Y  = make_g   [[c_0       ; minus c_i  ];
                     [c_i       ; c_0        ]]
let g_Z  = make_g   [[c_1       ; c_0        ];
                     [c_0       ; minus c_1  ]] 
let g_H  = make_g   [[c_h       ; c_h        ];
                     [c_h       ; minus (c_h)]]
                     
(* these two are intended to be like rotations. Unlike H, Rz*Rz<>I *)

let g_Rz = make_g   [[c_f       ; minus c_g  ];
                     [c_g       ; c_f        ]]
let g_G  = make_g   [[c_g       ; minus c_f  ];
                     [c_f       ; c_g        ]]

(* experimental Rx(pi/8) gate *)

let g_Rx = make_g   [[c_1       ; c_0        ];
                     [c_0       ; C(S_f,S_g) ]]
                     
let g_Phi = function (* as Pauli *)
  | 0 -> g_I
  | 1 -> g_X
  | 2 -> g_Y  
  | 3 -> g_Z  
  | i -> raise (Disaster ("** _Phi(" ^ string_of_int i ^ ")"))

let g_Swap =
  make_g [[c_1; c_0; c_0; c_0];
          [c_0; c_0; c_1; c_0];
          [c_0; c_1; c_0; c_0];
          [c_0; c_0; c_0; c_1]]
          
let g_Toffoli = (* tediously, sorry *)
  make_g  [[c_1; c_0; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_1; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_1; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_1; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_1; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_1; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_0; c_1 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_1; c_0 ]]
           
let g_Fredkin = (* tediously, sorry *)
  make_g  [[c_1; c_0; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_1; c_0; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_1; c_0; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_1; c_0; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_1; c_0; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_1; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_1; c_0; c_0 ];
           [c_0; c_0; c_0; c_0; c_0; c_0; c_0; c_1 ]]
           
let make_C g = 
  let m = matrix_of_gate g in
  make_g  [[c_1; c_0; c_0         ; c_0         ];
           [c_0; c_1; c_0         ; c_0         ];
           [c_0; c_0; ?..m z_0 z_0; ?..m z_0 z_1];
           [c_0; c_0; ?..m z_1 z_0; ?..m z_1 z_1]]
    
let g_CX   = make_C g_X
let g_CY   = make_C g_Y
let g_CZ   = make_C g_Z 
let g_Cnot = g_CX
                      
let g_1 = make_g [[c_1]] (* a unit for folding *)
let g_0 = make_g [[c_0]] (* another unit for folding, maybe *)

let m_1 = make_m [[c_1]]
let m_0 = make_m [[c_0]]

let func_I (n:int) = 
  Z.(let nrc = z_1 lsl n in
     let rcf i = [(i,c_1)] in
     FuncM ((Printf.sprintf "I⊗⊗%d" n), nrc, nrc, 
            (fun i j -> if i=j then c_1 else c_0), 
            Some (c_0,rcf, rcf)
           )
    )

let func_H (n:int) = 
  Z.(let sn = S_h n in
     let f i j = 
       C ((if Stdlib.(land) (popcount (i land j)) 1 = 1 then S_neg sn else sn), S_0)
     in
     let gsize = z_1 lsl n in
     FuncM ((Printf.sprintf "H⊗⊗%d" n), gsize, gsize, f, None)
   )
   
(* ******************* gate, matrix, vector arithmetic ****************************)

(* note that gates are square matrices, but we also have unsquare matrices *)

let init_v n f = Array.init n f
let init_m n m f = Array.init m (fun i -> Array.init m (f i))

let exists_dv p v = _for_exists 0 1 (Array.length v) (fun i -> p (Z.of_int i) v.(i))
let exists_m p = function
  | DenseM m            -> exists_dv (fun i row -> exists_dv (fun j x -> p i j x) row) m
  | SparseM (nc,sv,cvv) -> exists_dv (fun i cv -> let row = SparseV (nc,sv,cv) in
                                                  _for_existsZ z_0 z_1 nc (fun j -> p i j (?.row j))
                                     ) cvv
  | FuncM (_,nr,nc,f,_) -> _for_existsZ z_0 z_1 nr (fun i -> _for_existsZ z_0 z_1 nc (fun j -> p i j (f i j)))

(* from this point on, sparse matrices with non-zero sv complicate the coding. Remember
   that sparse techniques save space; sv=c_0 also saves time. 
 *)
 
let tensor_dvdv va vb =
  let na = Array.length va in
  let nb = Array.length vb in
  let vr = Array.make (na*nb) c_0 in
  for i = 0 to na-1 do 
    for j = 0 to nb-1 do vr.(i*nb+j) <- cprod va.(i) vb.(j) done
  done;
  vr

(* gives a cv length na*:nb, sv=cprod sva svb. Obviously a good thing if sva=svb=c_0 *)
let tensor_cvcv na sva cva nb svb cvb =
  let sv' = cprod sva svb in
  let shift k = if k=z_0 then (fun v -> v) else  List.map (fun (i,y) -> i+:k, y) in
  let mult x = if x=c_0 && sv'=c_0 then (fun _ -> []) else List.map (fun (i,y) -> i, cprod x y) in 
  let defaultv = mult sva cvb in
  let svvs =
    if defaultv=[] then (fun k n vs -> vs) else
    let rec svvs k n vs =
      if k=:n then vs else svvs (k+:z_1) n (shift (k*:nb) defaultv::vs) 
    in
    svvs
  in
  let rec f vs k = function 
    | []        -> List.concat (List.rev (svvs k na vs))
    | (i,x)::cv -> let vs = svvs k i vs in
                   let v = shift (i*:nb) (sparse_elements_cv (cprod x svb) sv' nb (mult x cvb)) in 
                   f (v::vs) (i+:z_1) cv
  in
  f [] z_0 cva
  
let tensor_vv va vb =
  let na = vsize va in
  let nb = vsize vb in
  match va, vb with
  | SparseV (_,sva,cva), SparseV (_,svb,cvb) -> SparseV (na*:nb, cprod sva svb, tensor_cvcv na sva cva nb svb cvb)
  | SparseV (_,sva,cva), _                   -> let svb,_ = svfreq_v vb in
                                                maybe_dense_v (cprod sva svb) (na*:nb)
                                                              (tensor_cvcv na sva cva nb svb (sparse_elements_v svb vb))
  | _                  , SparseV (_,svb,cvb) -> let sva,_ = svfreq_v va in
                                                maybe_dense_v (cprod sva svb) (na*:nb)
                                                              (tensor_cvcv na sva (sparse_elements_v sva va) nb svb cvb)
  | DenseV  dva        , DenseV  dvb         -> maybe_sparse_v (tensor_dvdv dva dvb)


let tensor_nvnv (mA,vA) (mB,vB) = (rprod mA mB, tensor_vv vA vB)
  
let tensor_qq (mA,vA as nvA) (mB,vB as nvB) =
  let mR, vR = tensor_nvnv nvA nvB in
  if !verbose_qcalc then Printf.printf "%s ⊗ %s -> %s\n"
                                       (string_of_ket (mA,vA))
                                       (string_of_ket (mB,vB))
                                       (string_of_ket (mR,vR));
  mR,vR

(* func_tensor works with div and mod, because I think I can afford them, which means I don't have to insist on gates *)

let tensor_ff nr2 nc2 f1 f2 i = Z.(tensor_cvcv nc2 (f1 (i/nr2)) (f2 (i mod nr2)))
let tensor_ff nca sva rfa ncb svb rfb nrb i = Z.(tensor_cvcv nca sva (rfa (i/nrb)) ncb svb (rfb (i mod nrb)))

let func_tensor_mf m id nr nc f rfopt =
  Z.(let nrm = rsize m in
     let ncm = csize m in
     let prodf i j =
       cprod (?..m (i / nr) (j / nc)) (f (i mod nr) (j mod nc))
     in
     let rowfopt = 
       match rowfopt_m m, rfopt with
       | Some (svm,rfm,cfm), Some (sv,rf,cf) -> Some (cprod svm sv, tensor_ff ncm svm rfm nc sv rf nr, tensor_ff nrm svm cfm nr sv cf nc)
       | _                                   -> None
     in
     FuncM ((Printf.sprintf "%s⊗(%s)" (string_of_matrix m) id), nrm*nr, ncm*nc, prodf, rowfopt)
   )
   
let func_tensor_fm id nr nc f rfopt m =
  Z.(let nrm = rsize m in
     let ncm = csize m in
     let prodf i j =
       cprod (f (i / nrm) (j / ncm)) (?..m (i mod nrm) (j mod ncm))
     in
     let rowfopt = 
       match rfopt, rowfopt_m m with
       | Some (sv,rf,cf), Some (svm,rfm,cfm) -> Some (cprod sv svm, tensor_ff nc sv rf ncm svm rfm nrm, tensor_ff nr sv cf nrm svm cfm ncm)
       | _                                   -> None
     in
     FuncM ((Printf.sprintf "%s⊗(%s)" id (string_of_matrix m)), nr*nrm, nc*ncm, prodf, rowfopt)
    )

let tensor_sparse_mm nra nca sva cvva nrb ncb svb cvvb = 
  try let inrb = Z.to_int nrb in 
      SparseM (nca*:ncb, cprod sva svb, Array.init (Z.to_int (nra*:nrb)) 
                                                   (fun i -> tensor_cvcv nca sva cvva.(i/inrb) ncb svb cvvb.(i mod inrb))
              )
  with Z.Overflow -> raise (Disaster (Printf.sprintf "tensor_sparse_mm %s %s" (string_of_zint nra) (string_of_zint nrb)))
  
let tensor_mm mA mB =
  if !verbose_qcalc then Printf.printf "tensor_mm %s %s = " (string_of_matrix mA) (string_of_matrix mB);
  let m = if mA=g_1 then mB else
          if mB=g_1 then mA else
            (let nra, nca = rsize mA, csize mA in
             let nrb, ncb = rsize mB, csize mB in
             match mA, mB with
             | _                   , FuncM (id,_,_,f,opt) -> func_tensor_mf mA id nrb ncb f opt
             | FuncM (id,_,_,f,opt), _                    -> func_tensor_fm id nra nca f opt mB
             | SparseM (_,sva,cvva), SparseM (_,svb,cvvb) -> tensor_sparse_mm nra nca sva cvva nrb ncb svb cvvb
             | SparseM (_,sva,cvva), DenseM  dmb          -> let svb,_ = svfreq_m mB in
                                                             let cvvb = cvv_of_dm svb dmb in
                                                             tensor_sparse_mm nra nca sva cvva nrb ncb svb cvvb
             | DenseM  dma         , SparseM (_,svb,cvvb) -> let sva,_ = svfreq_m mA in
                                                             let cvva = cvv_of_dm sva dma in
                                                             tensor_sparse_mm nra nca sva cvva nrb ncb svb cvvb
             | DenseM  dma         , DenseM  dmb          -> 
                 try 
                     let nra, nca = Z.to_int nra, Z.to_int nca in
                     let nrb, ncb = Z.to_int nrb, Z.to_int ncb in
                     let dmc = init_m (nra*nrb) (nca*ncb) (fun _ _ -> c_0) in
                     for i = 0 to nra-1 do
                       for j = 0 to nca-1 do
                         let aij = dma.(i).(j) in
                         for m = 0 to nrb-1 do
                           for p = 0 to ncb-1 do
                             dmc.(i*nrb+m).(j*ncb+p) <- cprod aij dmb.(m).(p)
                           done (* p *)
                         done (* n *)
                       done (* j *)
                     done (* i *);
                     maybe_sparse_m dmc
                 with Z.Overflow -> raise (Disaster (Printf.sprintf "tensor_mm DenseM(%s,%s) DenseM(%s,%s)" 
                                                            (string_of_zint nra) (string_of_zint nca)
                                                            (string_of_zint nrb) (string_of_zint ncb)
                                                    )
                                          )
            )  
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix m);
  m

let tensor_gg = tensor_mm

let fpow f one v n =
  List.fold_left f one (Listutils.tabulate n (const v))

let tensorpow_g = fpow tensor_gg g_1 
let tensorpow_nv = fpow tensor_nvnv nv_1
let tensorpow_m = fpow tensor_mm m_1

let track_dotprod = false

(* multiplication of sparse vectors ho hum *)
(* much more complicated now that sv is not always zero *)

(* this gives you a cv with sv=sva*svb *)
let dotprod_cvcv n sva cva svb cvb =
  if track_dotprod && (!verbose || !verbose_qcalc) then 
       Printf.printf "dotprod_cvcv %s %s %s %s %s = " (string_of_zint n) (string_of_csnum sva) (string_of_cv cva) 
                                                                         (string_of_csnum svb) (string_of_cv cvb); 
  let sv = cprod sva svb in
  let svs =
    if sv=c_0 then (fun k n vs -> vs) else
    let rec svs k n vs =
      if k=:n then vs else svs (k+:z_1) n (sv::vs) 
    in
    svs
  in
  let vadd v vs = if v=c_0 then vs else v::vs in
  let rec f vs k cva cvb =
    Z.(match cva, cvb with
       | (i,x)::ixs, (j,y)::jys -> if i<j then f (vadd (cprod x svb) (svs k i vs)) (i+z_1) ixs cvb else
                                   if i=j then f (vadd (cprod x y)   (svs k i vs)) (i+z_1) ixs jys else
                                               f (vadd (cprod sva y) (svs k j vs)) (j+z_1) cva jys
       | (i,x)::ixs, []         -> f (vadd (cprod x svb) (svs k i vs)) (i+z_1) ixs cvb 
       | []        , (j,y)::jys -> f (vadd (cprod sva y) (svs k j vs)) (j+z_1) cva jys
       | _                      -> let vs = svs k n vs in
                                   let r = simplify_csum vs in
                                   if track_dotprod && (!verbose || !verbose_qcalc) then 
                                     Printf.printf "(vs = %s; csum=%s) " (bracketed_string_of_list string_of_csnum vs) (string_of_csnum r); 
                                   r
     )
  in
  let r = f [] z_0 cva cvb in
  if track_dotprod && (!verbose || !verbose_qcalc) then Printf.printf "%s\n" (string_of_csnum r); 
  r

let dense_dotprod va vb =
  simplify_csum (List.map (uncurry2 cprod) (List.combine (Array.to_list va) (Array.to_list vb)))
  
let dotprod_vv vA vB =
  let n = vsize vA in
  if n<>vsize vB then 
    raise (Disaster (Printf.sprintf "dotprod size mismatch %s*%s" (string_of_vector vA) (string_of_vector vB)));
  match vA, vB with
  | SparseV (_,sva,cva), SparseV (_,svb,cvb) -> dotprod_cvcv n sva cva svb cvb
  | SparseV (_,sva,cva), DenseV  dvb         -> let svb,_ = svfreq_v vB in
                                                dotprod_cvcv n sva cva svb (sparse_elements_dv svb dvb)
  | DenseV  dva        , SparseV (_,svb,cvb) -> let sva,_ = svfreq_v vA in
                                                dotprod_cvcv n sva (sparse_elements_dv sva dva) svb cvb
  | DenseV  dva        , DenseV  dvb         -> dense_dotprod dva dvb
  
let rowcolprod nc row col =
  let els = Listutils.tabulate (my_to_int nc "rowcolprod") (fun j -> cprod (row (Z.of_int j)) (col (Z.of_int j))) in
  simplify_csum els

let mult_nv cn v =
  if cn=c_0 then SparseV (vsize v, c_0, []) 
  else
    match v with 
    | DenseV  v         -> DenseV (Array.map (fun x -> cprod cn x) v)
    | SparseV (n,sv,cv) -> SparseV (n, cprod cn sv, List.map (fun (i,x) -> i, cprod cn x) cv)

module OrderedZ = struct type t = zint
                         let compare = Z.compare
                         let to_string = string_of_zint
                  end
                      
module ZSet = MySet.Make (OrderedZ)

(* this is the point of SparseV (and partly SparseM and FuncM): multiplying sparse row by sparse column. *)

(* gives a cv with sv=cprod sv svv *)
let mult_cvvcv nr nc sv rf cf svv cv = 
  let sv' = cprod sv svv in
  let do_row nxs i = 
    let x = dotprod_cvcv nc sv (rf i) svv cv in
    if x=sv' then nxs else (i,x)::nxs
  in
  (* find the rows where the matrix has a value that goes with something in cv *)
  let rs = if sv=c_0 && svv=c_0 then
             (let rset = List.fold_left (fun rset (c,_) -> List.fold_left (fun rset (r,_) -> ZSet.add r rset) 
                                                                          rset 
                                                                          (cf c)
                                        ) 
                                        ZSet.empty 
                                        cv 
              in
              List.sort Z.compare (ZSet.elements rset)
             )
           else tabulate (Z.to_int nr) Z.of_int
  in
  maybe_dense_v sv' nr (List.rev (List.fold_left do_row [] rs))
  
let mult_mv m v =
  if !verbose_qcalc then 
    (Printf.printf "mult_mv %s %s = " (string_of_matrix m) (string_of_vector v); flush_all());
  let nr = rsize m in
  let nc = csize m in
  if vsize v <> nc then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_mv %s %s"
                                 (string_of_matrix m)
                                 (string_of_vector v)
                 )
          );
  let default () = maybe_sparse_v (Array.init (my_to_int nc "mult_mv default") (fun i -> rowcolprod nc (?..m (Z.of_int i)) (?.v))) in
  let v' = match m, v with
           | SparseM (_,svm,cvv)            , SparseV (_,svv,cv) -> 
               mult_cvvcv nr nc svm (Array.get cvv <.> Z.to_int) (Array.get (transpose_cvv cvv) <.> Z.to_int) svv cv
           | FuncM (_,_,_,_,Some (sv,rf,cf)), SparseV (_,svv,cv) -> 
               mult_cvvcv nr nc sv rf cf svv cv
           | _                                                   -> 
               default ()
  in
  if !verbose_qcalc then 
    (Printf.printf "%s\n" (string_of_ket (S_h 0, v')); flush_all ());
  v'

let mult_gnv g (n,v) = n, mult_mv (matrix_of_gate g) v

(* This is not very optimised. But not a priority *)
(* it even destroys FuncM. Ho hum. *)
let mult_mm mA mB = 
  if !verbose_qcalc then 
    Printf.printf "mult_mm %s %s = " (string_of_matrix mA) (string_of_matrix mB);
  let m = rsize mA in
  let n = csize mA in
  if n<>rsize mB then
    raise (Error (Printf.sprintf "matrix size mismatch in multiply: %s * %s"
                                 (string_of_matrix mA)
                                 (string_of_matrix mB)
                 )
          );
  let p = csize mB in
  let mC = try match mA, mB with
               | SparseM (ncA,svA,cvvA), SparseM (ncB,svB,cvvB) -> 
                   let sv' = cprod svA svB in
                   let rvvB = transpose_cvv cvvB in
                   let cvv = Array.make (Z.to_int m) [] in
                   (* for rather than _forZ because cvvA and cvvB are indexed within int bounds *)
                   for i = 0 to Z.to_int m-1 do
                     for j = 0 to Z.to_int p-1 do
                       let x = dotprod_cvcv n svA cvvA.(i) svB rvvB.(j) in
                       if x<>sv' then cvv.(i) <- (Z.of_int j,x)::cvv.(i)
                     done
                   done;
                   maybe_dense_m sv' p (Array.map List.rev cvv)
               | _                                        -> 
                   maybe_sparse_m (init_m (Z.to_int m) (Z.to_int p) 
                                          (fun i j -> rowcolprod n (?..mA (Z.of_int i)) (revargs ?..mB (Z.of_int j)))
                                  )
             with Z.Overflow -> raise (Disaster (Printf.sprintf "mult_mm (%s,%s) (%s,%s)"
                                                                    (string_of_zint (rsize mA)) (string_of_zint (csize mA))
                                                                    (string_of_zint (rsize mB)) (string_of_zint (csize mB))
                                                )
                                      )
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix mC);
  mC
  
let mult_nm cn m = 
  if !verbose || !verbose_qcalc then
    (Printf.printf "mult_nm %s %s = " (string_of_csnum cn) (string_of_matrix m); 
     flush_all();
    );
  let r = (let do_cv cv = List.map (fun (i,x) -> i,cprod cn x) cv in
           match m with
           | SparseM (n, sv, cvv)         -> SparseM (n, cprod sv cn, Array.map do_cv cvv)
           | FuncM (id, rs, cs, f, rfopt) -> let id = Printf.sprintf "%s*%s" (string_of_csnum cn) id in
                                             FuncM (id, rs, cs, cprod cn <..> f, 
                                                     rfopt &~~ (fun (sv,rf,cf) -> Some (cprod sv cn, do_cv <.> rf, do_cv <.> cf))
                                                   )
           | DenseM dm as mA              -> let m = Z.to_int (rsize mA) in
                                             let n = Z.to_int (csize mA) in
                                             maybe_sparse_m (init_m m n (fun i j -> cprod cn (dm.(i).(j))))
          )
  in
  if !verbose || !verbose_qcalc then
    (Printf.printf "%s\n" (string_of_matrix r); 
     flush_all();
    );
  r

let mult_gg = mult_mm

let mult_kb (km, kv as k) (bm, bv as b) =
  if !verbose || !verbose_qcalc then
    (Printf.printf "mult_kb %s %s = " (string_of_ket k) (string_of_bra b); 
     flush_all();
    );
  let r = (let n = vsize kv in
           if vsize bv<>n then
             raise (Error (Printf.sprintf "size mismatch in ket*bra: %s*%s\n%s\n%s" 
                                                 (string_of_zint (vsize kv)) (string_of_zint (vsize bv))
                                                 (string_of_ket k) (string_of_bra b)
                          )
                   );
           if bm<>S_h 0 || km<>S_h 0 then 
             raise (Error (Printf.sprintf "bra*ket multiplication with non-unit modulus\n%s\n%s"
                                                 (string_of_ket k) (string_of_bra b)
                          )
                   );
           try maybe_sparse_m (init_m (Z.to_int n) (Z.to_int n) (fun i j -> cprod (?.kv (Z.of_int i)) (?.bv (Z.of_int j))))
           with Z.Overflow -> raise (Disaster (Printf.sprintf "Overflow in mult_kb %s %s" (string_of_zint n) (string_of_zint n)))
          )
  in
  if !verbose || !verbose_qcalc then
    (Printf.printf "%s\n" (string_of_matrix r); 
     flush_all();
    );
  r

(* conjugate transpose: transpose and piecewise complex conjugate *)
let cconj_cv = List.map (fun (i,x) -> i, cconj x)

let dagger_m = function
  | SparseM (nc, sv, cvv)    -> SparseM (nc, cconj sv, Array.map cconj_cv (transpose_cvv cvv))
  | DenseM dm as mA          -> let m = Z.to_int (rsize mA) in
                                let n = Z.to_int (csize mA) in
                                DenseM (init_m m n (fun i j -> cconj (dm.(j).(i))))
  | FuncM (id, rn, cn, f, opt) -> let id = Printf.sprintf "(%s)†" id in
                                FuncM (id, rn, cn, cconj <..> revargs f, 
                                        opt &~~ (fun (sv, rf, cf) -> Some (cconj sv, cconj_cv <.> cf, cconj_cv <.> rf))
                                      ) 

let dagger_g = dagger_m

let addsub_cvcv f s svA cvA svB cvB =
  let rec doit els cvA cvB =
    match cvA, cvB with
    | (i,x)::ixs, (j,y)::jys -> if i<j then doit ((i, f x   svB)::els) ixs cvB else
                                if i=j then doit ((i, f x   y  )::els) ixs jys else
                                            doit ((j, f svA y  )::els) cvA jys
    | (i,x)::ixs, []         ->             doit ((i, f x   svB)::els) ixs cvB
    | []        , (j,y)::jys ->             doit ((j, f svA y  )::els) cvA jys
    | []        , []         ->             List.rev els
  in
  doit [] cvA cvB
  
let addsub_ff f s svA rfA svB rfB i = addsub_cvcv f s svA (rfA i) svB (rfB i)

let addsub_mm f s mA mB =
  let m = rsize mA in
  let n = csize mA in
  if m<>rsize mB || n<>csize mB then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): %s %s %s"
                                 (string_of_matrix mA)
                                 s
                                 (string_of_matrix mB)
                 )
          );
  match mA, mB with
  | SparseM (_,svA,cvvA)   , SparseM (_,svB,cvvB)    -> 
      let cvv = Array.init (Z.to_int m) (fun i -> addsub_cvcv f s svA cvvA.(i) svB cvvB.(i)) in
      maybe_dense_m (f svA svB) n cvv
  | FuncM (idA,_,_,fA,optA), FuncM (idB,_,_,fB,optB) -> 
      let id = Printf.sprintf "(%s)%s(%s)" idA s idB in
      let opt = match optA, optB with
                | Some (svA,rfA,cfA), Some (svB,rfB,cfB) -> Some (f svA svB, addsub_ff f s svA rfA svB rfB, 
                                                                             addsub_ff f s svA cfA svB cfB
                                                                 )
                | _                              -> None
      in
      FuncM (id, m, n, (fun i j -> f (fA i j) (fB i j)), opt)
  | _                                                -> 
      try maybe_sparse_m (init_m (Z.to_int m) (Z.to_int n) 
                                 (fun i j -> f (?..mA (Z.of_int i) (Z.of_int j)) (?..mB (Z.of_int i) (Z.of_int j)))
                         )
      with Z.Overflow -> raise (Disaster (Printf.sprintf "Overflow in addsum_mm (%s*%s)" (string_of_zint m) (string_of_zint n)))

let add_mm = addsub_mm csum "+"
let sub_mm = addsub_mm cdiff "-"

let engate mA =
  let m = rsize mA in
  let n = csize mA in
  if m<>:n then raise (Error (Printf.sprintf "non-square engate %s" (string_of_matrix mA)));
  (try ignore (log_2 m) 
   with _ -> raise (Error (Printf.sprintf "matrix size %s is not power of 2 in engate %s" (string_of_zint m) (string_of_matrix mA)))
  );
  let mB = mult_mm mA (dagger_m mA) in
  if exists_m (fun i j x -> j=:i && x<>c_1 || j<>:i && x<>c_0) mB then
    raise (Error (Printf.sprintf "non-unitary engate %s\n(m*m† = %s)" (string_of_matrix mA) (string_of_matrix mB)));
  gate_of_matrix mA