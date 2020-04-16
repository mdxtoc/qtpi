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

exception Error of string
exception Disaster of string

(* find log_2 n, but only if n is a power of 2 -- else raise Invalid_argument *)
let log_2 n =
  let rec find_twopower r i =
    if i=1               then r                    else
    if i=0 || i land 1=1 then raise (Invalid_argument ("log_2 " ^ string_of_int n)) else
                              find_twopower (r+1) (i lsr 1)
  in
  find_twopower 0 n

(* i^n -- only for positive n *)
let intexp i n =  
  let rec exp r n = if n<=0 then r else exp (i*r) (n-1) in
  exp 1 n
  
(* an n-bit mask, given an index -- in effect 2^n-1*)
let mask n = intexp 2 n - 1

(* *********************** vectors, matrices,gates ************************************ *)

type dvec  = csnum array
and  cvec  = (int * csnum) list                 (* assoc list *)

type vector = 
  | DenseV   of dvec                            (* always 2^n-sized, but we don't have existential type for that *)
  | SparseV  of int * cvec                      (* size, default value, values *)

and matrix = 
  | DenseM of dmat                              (* not necessarily square *)
  | SparseM of int * cvec array                 (* csize, sparse rows *)
  | FuncM  of string * int * int * (int -> int -> csnum) * ((int -> cvec) * (int -> cvec)) option
                                                (* rsize, csize, element function, sparse row/column option *)

and dmat = csnum array array

and nv = modulus * vector                       (* modulus, vector: meaning 1/sqrt(modulus)(vec) *)

and modulus = snum 

and gate = matrix                               (* gates must be square, unitary and 2^n-sized, 
                                                   but to say that we would need an existential type.
                                                 *)

let string_of_cv assoc = Printf.sprintf "[%s]" (string_of_assoc string_of_int string_of_csnum ":" ";" assoc)

let vsize = function
  | DenseV  v     -> Array.length v
  | SparseV (n,_) -> n

let nvsize (_,v) = vsize v
        
let rsize = function
  | DenseM m            -> Array.length m
  | SparseM (nc, cvs)   -> Array.length cvs
  | FuncM  (_,nr,_,_,_) -> nr

let csize = function
  | DenseM m            -> if Array.length m = 0 then 0 else Array.length m.(0)
  | SparseM (nc, cvs)   -> nc
  | FuncM  (_,_,nc,_,_) -> nc

let gsize = rsize

(* cvecs are ordered ... *)

let cvseg n m cv = (* n<=i<m, natch *)
  takewhile (fun (i,_) -> i<m) (dropwhile (fun (i,_) -> i<n) cv)
  
let rec find_cv xs i =
  match xs with
  | (j,x)::xs -> if i<j then c_0 else if i=j then x else find_cv xs i
  | []        -> c_0

(* accessing vectors whatever the form *)
let (?.) v i = 
  match v with 
  | DenseV  v       -> v.(i)
  | SparseV (_, cv) -> find_cv cv i

(* accessing matrices whatever the form *)
let (?..) m i j =
  match m with
  | DenseM m           -> m.(i).(j)
  | SparseM (_,cvv)    -> find_cv (cvv.(i)) j
  | FuncM  (_,_,_,f,_) -> f i j

let densify_cv n cv = Array.init n (find_cv cv)

let densify_v =
  function
  | DenseV v       -> v
  | SparseV (n,cv) -> densify_cv n cv
  
let dense_countzeros_v n m v = (* from n to m-1, natch *)
  _for_fold_left n 1 m 0 (fun nzs i -> if v.(i)=c_0 then nzs+1 else nzs)
  
let countzeros_v n m v = (* from n to m-1, natch *)
  if n>=m then 0 else match v with
                      | DenseV  v      -> dense_countzeros_v n m v
                      | SparseV (_,cv) -> let cv' = cvseg n m cv in m-n-List.length cv'

let cv_of_dv dv = 
  let nxs = Array.to_list (Array.mapi (fun i x -> i,x) dv) in
  List.filter (fun (_,x) -> x<>c_0) nxs
  
let maybe_sparse_v v =
  let n = Array.length v in
  let freq = dense_countzeros_v 0 n v in
  if freq*4>3*n then SparseV (n, cv_of_dv v)
                else DenseV  v

let dv_of_cv n cv =
  let dv = Array.make n c_0 in
  List.iter (fun (i,x) -> dv.(i) <- x) cv;
  dv

let maybe_dense_v n cv =
  if List.length cv*4>n then DenseV (dv_of_cv n cv)
                        else SparseV (n, cv)

let sparse_elements_dv v = List.filter (fun (_,x) -> x<>c_0) (Array.to_list (Array.mapi (fun i x -> i,x) v))

let sparse_elements_v vV =
  match vV with
  | SparseV (_,cv) -> cv
  | DenseV  v      -> sparse_elements_dv v

let vseg n m vv = (* from n to m-1, natch *)
  match vv with
  | DenseV  v       -> DenseV (Array.init (m-n) (fun i -> v.(n+i)))
  | SparseV (_, cv) -> SparseV (m-n, cvseg n m cv)

let zeroseg n m vv = (* from n to m-1, natch *) (* ** uses assignment ** *) 
  match vv with
  | DenseV  v       -> _for n 1 m (fun i -> v.(i) <- c_0);
                       vv
  | SparseV (k, cv) -> SparseV (k, cvseg 0 n cv @ cvseg m k cv)

let map_v f = 
  function
  | SparseV (n,cv) when f c_0 = c_0 -> SparseV (n, List.map (fun (i,x) -> i, f x) cv)
  | v                               -> maybe_sparse_v (Array.map f (densify_v v))

let intersect_cv cvA cvB =
  let rec inter rs cvA cvB =
    match cvA, cvB with
    | (i,x)::ixs, (j,y)::jys -> if i<j then inter rs            ixs cvB else
                                if i=j then inter ((i,(x,y))::rs) ixs jys else
                                            inter rs            cvA jys
    | _                      -> List.rev rs
  in
  inter [] cvA cvB
  
let union_cv cvA cvB =
  let rec union rs cvA cvB =
    match cvA, cvB with
    | (i,x)::ixs, (j,y)::jys -> if i<j then union ((i,(x  ,c_0))::rs) ixs cvB else
                                if i=j then union ((i,(x  ,y  ))::rs) ixs jys else
                                            union ((j,(c_0,y  ))::rs) cvA jys
    | _                      -> List.rev rs
  in
  union [] cvA cvB
  
type bksign = PVBra | PVKet

let string_of_nv bksign = 
  let so_v v =
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
                      | SparseV (_, cv) -> List.fold_left estringf [] cv 
                      | DenseV  dv      -> _for_fold_left 0 1 n [] (fun ss i-> estringf ss (i,dv.(i)))
       in
       match estrings with
       | []  -> "?..empty nv?.."
       | [e] -> e
       | _   -> Printf.sprintf "(%s)" (sum_separate (List.rev estrings))
      )
    else
      match v with
      | DenseV  v      -> let estrings = Array.fold_right (fun s ss -> string_of_csnum s::ss) v [] in
                          Printf.sprintf "DenseV⟨%s⟩" (String.concat "," estrings)
      | SparseV (n,cv) -> Printf.sprintf "SparseV(%d,[%s])" n (string_of_cv cv)
  in
  let normalised_sign vv = 
    let doit x = 
      match (string_of_csnum x).[0] with
      | '-' -> so_v (map_v cneg vv)
      | _   -> so_v vv 
    in
    match vv with
    | SparseV (_, (_,x)::_) -> doit x
    | SparseV (_, []      ) -> so_v vv
    | DenseV  v             -> let xs = dropwhile ((=) c_0) (Array.to_list v) in
                               match xs with
                               | x::xs -> doit x
                               | []    -> so_v vv
  in
  function
  | S_1, vv -> normalised_sign vv
  | vm , vv -> Printf.sprintf "<<%s>>%s" (string_of_snum vm) (normalised_sign vv)
  
let string_of_bra = string_of_nv PVBra
let string_of_ket = string_of_nv PVKet

let string_of_vector v = string_of_ket (S_1,v)

let string_of_matrix = function
  | DenseM m -> 
      let strings_of_row r = Array.fold_right (fun s ss -> string_of_csnum s::ss) r [] in
      let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
      let rwidth r = List.fold_left max 0 (List.map String.length r) in
      let width = List.fold_left max 0 (List.map rwidth block) in
      let pad s = s ^ String.make (width - String.length s) ' ' in
      let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
      Printf.sprintf "\n{%s}\n" block
  | SparseM (nc,cvv) ->   
      Printf.sprintf "SparseM %d ⟨%s⟩\n" nc (string_of_list string_of_cv "\n" (Array.to_list cvv))
  | FuncM (id,rn,cn,_,opt) ->
      Printf.sprintf "FuncM(%s,%d,%d,_,%s)" id rn cn (Optionutils.string_of_option (fun _ -> "_,_") opt)
      
let string_of_gate = string_of_matrix

let statistics_v vV =
  let stats = CsnumHash.create 1000 in
  let get v = try CsnumHash.find stats v with _ -> (let r = ref 0 in CsnumHash.add stats v r; r) in
  let count v = let r = get v in r:=!r+1 in
  let n = vsize vV in
  for i = 0 to n-1 do
    count (?.vV i)
  done;
  let compare (vi,i) (vj,j) = ~-(Stdlib.compare (i,vi) (j,vj)) in
  List.sort compare (List.map (fun (v,r) -> v,!r) (CsnumHash.to_assoc stats))

let statistics_nv (_,v) = statistics_v v

let statistics_m mM =
  let stats = CsnumHash.create 1000 in
  let get v = try CsnumHash.find stats v with _ -> (let r = ref 0 in CsnumHash.add stats v r; r) in
  let count v = let r = get v in r:=!r+1 in
  let n,m = rsize mM, csize mM in
  for i = 0 to n-1 do
    for j = 0 to m-1 do
      count (?..mM i j)
    done
  done;
  let compare (vi,i) (vj,j) = ~-(Stdlib.compare (i,vi) (j,vj)) in
  List.sort compare (List.map (fun (v,r) -> v,!r) (CsnumHash.to_assoc stats))

let countzeros_m dm = 
  let nr = Array.length dm in
  if nr=0 then 0
  else         Array.fold_left (Array.fold_left (fun n x -> if x=c_0 then n+1 else n)) 0 dm

let cvv_of_dm = Array.map cv_of_dv

let maybe_sparse_m dm =
  let m = DenseM dm in
  let nr = rsize m in
  let nc = csize m in
  let freq = countzeros_m dm in
  if freq*4 > 3*nr*nc then SparseM (nc, cvv_of_dm dm)
                      else m

let dm_of_cvv nc cvv =
  Array.map (dv_of_cv nc) cvv

let maybe_dense_m nc cvv =
  let nels = Array.fold_left (fun n cv -> n+List.length cv) 0 cvv in
  if nels*4 > Array.length cvv * nc then DenseM (dm_of_cvv nc cvv)
                                    else SparseM (nc, cvv)
    
let transpose_cvv cvv =
  let rvv = Array.map (fun cv -> PQueue.create (List.length cv+1)) cvv in
  Array.iteri (fun i cv -> List.iter (fun (j,x) -> PQueue.push rvv.(j) (i,x)) cv) cvv;
  Array.map PQueue.to_list rvv
  
module DmatH = struct type t = dmat 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = (fun dm -> string_of_matrix (DenseM dm))
               end
module DMatHash = MyHash.Make (DmatH)
                    
let rcftab = DMatHash.create (100)

let rowfopt_m = function
  | SparseM (n, cvv)          -> Some (Array.get cvv, Array.get (transpose_cvv cvv))
  | FuncM   (id,nr,nc,f,optf) -> optf
  | DenseM dm                 -> (* if we are asked, it's needed *)
                                 try Some (DMatHash.find rcftab dm) 
                                 with Not_found -> let cvv = cvv_of_dm dm in
                                                   let r = Array.get cvv, Array.get (transpose_cvv cvv) in
                                                   DMatHash.add rcftab dm r;
                                                   Some r
                       
(* ********************** build vectors, matrices, gates ******************************* *)

let minus  (C (x,y)) = (* only for local use, please *)
  let negate = function
    | S_0 -> S_0
    | s   -> S_neg s
  in
  C (negate x, negate y) 

let make_nv ss = S_1, DenseV (Array.of_list ss)

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
  make_g  [[c_1; c_0; c_0    ; c_0    ];
           [c_0; c_1; c_0    ; c_0    ];
           [c_0; c_0; ?..m 0 0; ?..m 0 1];
           [c_0; c_0; ?..m 1 0; ?..m 1 1]]
    
let g_CX   = make_C g_X
let g_CY   = make_C g_Y
let g_CZ   = make_C g_Z 
let g_Cnot = g_CX
                      
let g_1 = make_g [[c_1]] (* a unit for folding *)
let g_0 = make_g [[c_0]] (* another unit for folding, maybe *)

let m_1 = make_m [[c_1]]
let m_0 = make_m [[c_0]]

let func_I n = let nrc = 1 lsl n in
               let rcf i = [(i,c_1)] in
               FuncM ((Printf.sprintf "I⊗⊗%d" n), nrc, nrc, 
                      (fun i j -> if i=j then c_1 else c_0), 
                      Some (rcf, rcf)
                     )

let func_H n = 
  let rec bitcount r n = 
    if n=0 then r else bitcount (if n land 1 = 1 then r+1 else r) (n lsr 1)
  in
  let sn = S_h n in
  let f i j = 
    C ((if bitcount 0 (i land j) land 1 = 1 then S_neg sn else sn), S_0)
  in
  let gsize = 1 lsl n in
  FuncM ((Printf.sprintf "H⊗⊗%d" n), gsize, gsize, f, None)
  
(* ******************* gate, matrix, vector arithmetic ****************************)

(* note that gates are square matrices, but we also have unsquare matrices *)

let init_v n f = Array.init n f
let init_m n m f = Array.init m (fun i -> Array.init m (f i))

let exists_v p v = _for_exists 0 1 (Array.length v) (fun i -> p i v.(i))
let exists_m p = function
  | DenseM m            -> exists_v (fun i row -> exists_v (fun j x -> p i j x) row) m
  | SparseM (_,cvv)     -> exists_v (fun i -> List.exists (fun (j,x) -> p i j x)) cvv
  | FuncM (_,rn,cn,f,_) -> _for_exists 0 1 rn (fun i -> _for_exists 0 1 cn (fun j -> p i j (f i j)))

let tensor_dvdv va vb =
  let na = Array.length va in
  let nb = Array.length vb in
  let vr = Array.make (na*nb) c_0 in
  for i = 0 to na-1 do 
    for j = 0 to nb-1 do vr.(i*nb+j) <- cprod va.(i) vb.(j) done
  done;
  vr

let tensor_cvcv ncb cva cvb =
  List.concat (List.map (fun (i,x) -> List.map (fun (j,y) -> i*ncb+j, cprod x y) cvb) cva)
  
let tensor_vv vA vB =
  let nA = vsize vA in
  let nB = vsize vB in
  (* let shift k = if k=0 then (fun v -> v) else  List.map (fun (i,y) -> i+k, y) in
     let mult x = if x=c_0 then (fun _ -> []) else List.map (fun (i,y) -> i, cprod x y) in 
   *)
  let shift_mult k x = if x=c_0 then (fun _ -> []) 
                       else List.map (fun (i,y) -> i+k, cprod x y) 
  in (* can't resist an efficient composition *)
  let do_sparse cvA cvB = 
    let insert (i,x) = shift_mult (i*nB) x cvB in
    let nvs = List.map insert cvA in
    SparseV (nA*nB, List.concat nvs) 
  in
  match vA, vB with
  | SparseV (_, cvA), _               -> do_sparse cvA (sparse_elements_v vB)
  | _               , SparseV (_,cvB) -> do_sparse (sparse_elements_v vA) cvB
  | DenseV  va      , DenseV  vb      -> maybe_sparse_v (tensor_dvdv va vb)


let tensor_nvnv (mA,vA) (mB,vB) = (rprod mA mB, tensor_vv vA vB)
  
let tensor_qq (mA,vA as pvA) (mB,vB as pvB) =
  let mR, vR = tensor_nvnv pvA pvB in
  if !verbose_qcalc then Printf.printf "%s ⊗ %s -> %s\n"
                                       (string_of_ket (mA,vA))
                                       (string_of_ket (mB,vB))
                                       (string_of_ket (mR,vR));
  mR,vR

(* func_tensor works with div and mod, because I think I can afford them, which means I don't have to insist on gates *)

let tensor_ff nr2 nc2 f1 f2 i = tensor_cvcv nc2 (f1 (i/nr2)) (f2 (i mod nr2))

let func_tensor_mf m id nrB ncB f rfopt =
  let nrA = rsize m in
  let ncA = csize m in
  let prodf i j =
    cprod (?..m (i / nrB) (j / ncB)) (f (i mod nrB) (j mod ncB))
  in
  let rowfopt = 
    match rowfopt_m m, rfopt with
    | Some (mrf,mcf), Some (rf,cf) -> Some (tensor_ff nrB ncB mrf rf, tensor_ff ncB nrB mcf cf)
    | _                            -> None
  in
  FuncM ((Printf.sprintf "%s⊗(%s)" (string_of_matrix m) id), nrA*nrB, ncA*ncB, prodf, rowfopt)
  
let func_tensor_fm id nrA ncA f rfopt m =
  let nrB = rsize m in
  let ncB = csize m in
  let prodf i j =
    cprod (f (i / nrB) (j / ncB)) (?..m (i mod nrB) (j mod ncB))
  in
  let rowfopt = 
    match rfopt, rowfopt_m m with
    | Some (rf,cf), Some (mrf,mcf) -> Some (tensor_ff nrB ncB rf mrf, tensor_ff ncB nrB cf mcf)
    | _                            -> None
  in
  FuncM ((Printf.sprintf "%s⊗(%s)" id (string_of_matrix m)), nrA*nrB, ncA*ncB, prodf, rowfopt)

let tensor_sparse_mm nra nca cvva nrb ncb cvvb = 
  SparseM (nca*ncb, Array.init (nra*nrb) (fun i -> tensor_cvcv ncb cvva.(i/nrb) cvvb.(i mod nrb)))
  
let tensor_mm mA mB =
  if !verbose_qcalc then Printf.printf "tensor_mm %s %s = " (string_of_matrix mA) (string_of_matrix mB);
  let m = if mA=g_1 then mB else
          if mB=g_1 then mA else
            (let nra, nca = rsize mA, csize mA in
             let nrb, ncb = rsize mB, csize mB in
             match mA, mB with
             | _                   , FuncM (id,_,_,f,opt) -> func_tensor_mf mA id nrb ncb f opt
             | FuncM (id,_,_,f,opt), _                    -> func_tensor_fm id nra nca f opt mB
             | SparseM (_, cvva)   , SparseM (_, cvvb)    -> tensor_sparse_mm nra nca cvva nrb ncb cvvb
             | SparseM (_, cvva)   , DenseM  dmb          -> let cvvb = cvv_of_dm dmb in
                                                             tensor_sparse_mm nra nca cvva nrb ncb cvvb
             | DenseM  dma         , SparseM (_, cvvb)    -> let cvva = cvv_of_dm dma in
                                                             tensor_sparse_mm nra nca cvva nrb ncb cvvb
             | DenseM  dma         , DenseM  dmb          -> 
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

let track_innerprod = true

(* multiplication of sparse vectors ho hum *)
let innerprod_cvcv cvA cvB =
  if track_innerprod && (!verbose || !verbose_qcalc) then 
       Printf.printf "innerprod_cvcv %s %s = " (string_of_cv cvA) (string_of_cv cvB); 
  let rec mult r cvA cvB =
    match cvA, cvB with
    | (i,x)::ixs, (j,y)::jys -> if i<j then mult r                    ixs cvB else
                                if i=j then mult (csum r (cprod x y)) ixs jys else
                                            mult r                    cvA jys
    | _                      -> r
  in
  let r = mult c_0 cvA cvB in
  if track_innerprod && (!verbose || !verbose_qcalc) then Printf.printf "%s\n" (string_of_csnum r); 
  r

let dense_innerprod va vb =
  simplify_csum (List.map (uncurry2 cprod) (List.combine (Array.to_list va) (Array.to_list vb)))
  
let innerprod_vv vA vB = 
  if vsize vA<>vsize vB then 
    raise (Disaster (Printf.sprintf "innerprod size mismatch %s*%s" (string_of_vector vA) (string_of_vector vB)));
  match vA, vB with
  | SparseV (_,cvA), _                -> innerprod_cvcv cvA (sparse_elements_v vB)
  | _              , SparseV (_,cvB)  -> innerprod_cvcv (sparse_elements_v vA) cvB
  | DenseV  va     , DenseV  vb       -> dense_innerprod va vb
  
let rowcolprod n row col =
  let els = Listutils.tabulate n (fun j -> cprod (row j) (col j)) in
  simplify_csum els

let mult_nv cn v =
  if cn=c_0 then SparseV (vsize v, []) 
  else
    match v with 
    | DenseV  v      -> DenseV (Array.map (fun x -> cprod cn x) v)
    | SparseV (n,cv) -> SparseV (n, List.map (fun (i,x) -> i, cprod cn x) cv)
    
(* this is the point of SparseV (and partly SparseM and FuncM): multiplying sparse row by sparse column. *)
let mult_cvvcv nr rf cf cv = 
  let do_row nxs i = 
    let x = innerprod_cvcv (rf i) cv in
    if x=c_0 then nxs else (i,x)::nxs
  in
  (* find the rows where the matrix has a value that goes with something in cv *)
  let rs = List.rev (List.concat (List.fold_left (fun rss (i,_) -> (List.map fst (cf i))::rss) [] cv)) in
  maybe_dense_v nr (List.rev (List.fold_left do_row [] rs))
  
let mult_mv m v =
  if !verbose_qcalc then 
    (Printf.printf "mult_mv %s %s = " (string_of_matrix m) (string_of_ket (S_1,v)); flush_all());
  let n = vsize v in
  if csize m <> n then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_mv %s %s"
                                 (string_of_matrix m)
                                 (string_of_ket (S_1,v))
                 )
          );
  let default () = maybe_sparse_v (Array.init n (fun i -> rowcolprod n (?..m i) (?.v))) in
  let v' = match m, v with
           | SparseM (_, cvv)            , SparseV (_, cv) -> mult_cvvcv n (Array.get cvv) (Array.get (transpose_cvv cvv)) cv
           | FuncM (_,_,_,_,Some (rf,cf)), SparseV (_, cv) -> mult_cvvcv n rf cf cv
           | _                                            -> default ()
  in
  if !verbose_qcalc then 
    (Printf.printf "%s\n" (string_of_ket (S_1, v')); flush_all ());
  v'

let mult_gnv g (n,v) = n, mult_mv (matrix_of_gate g) v

(* This is not very optimised. But not a priority *)
(* it even destroys FuncM. Ho hum. *)
let mult_mm mA mB = 
  if !verbose_qcalc then 
    Printf.printf "mult_mm %s %s = " (string_of_matrix mA) (string_of_matrix mB);
  let m = rsize mA in
  let n = csize mA in
  let p = csize mB in
  if n<>rsize mB then
    raise (Error (Printf.sprintf "matrix size mismatch in multiply: %s * %s"
                                 (string_of_matrix mA)
                                 (string_of_matrix mB)
                 )
          );
  let mC = match mA, mB with
           | SparseM (ncA, cvvA), SparseM (ncB, cvvB) -> 
               let rvvB = transpose_cvv cvvB in
               let cvv = Array.make m [] in
               for i = 0 to m-1 do
                 for j = 0 to p-1 do
                   let x = innerprod_cvcv cvvA.(i) rvvB.(j) in
                   if x<>c_0 then cvv.(i) <- (j,x)::cvv.(i)
                 done
               done;
               maybe_dense_m p (Array.map List.rev cvv)
           | _                                        -> 
               maybe_sparse_m (init_m m p (fun i j -> rowcolprod n (?..mA i) (revargs ?..mB j)))
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix mC);
  mC
  
let mult_nm cn = 
  let do_cv cv = let cv' = List.map (fun (i,x) -> i,cprod cn x) cv in
                            List.filter (fun (i,x) -> x<>c_0) cv'
  in
  function
  | SparseM (n, cvv)             -> SparseM (n, Array.map do_cv cvv)
  | FuncM (id, rs, cs, f, rfopt) -> let id = Printf.sprintf "%s*%s" (string_of_csnum cn) id in
                                    FuncM (id, rs, cs, cprod cn <..> f, rfopt &~~ (fun (rf,cf) -> Some (do_cv <.> rf, do_cv <.> cf)))
  | DenseM dm as mA              -> let m = rsize mA in
                                    let n = csize mA in
                                    maybe_sparse_m (init_m m n (fun i j -> cprod cn (dm.(i).(j))))
  
let mult_gg = mult_mm

let mult_kb (km, kv as k) (bm, bv as b) =
  let n = vsize kv in
  if vsize bv<>n then
    raise (Error (Printf.sprintf "size mismatch in ket*bra: %d*%d\n%s\n%s" 
                                        (vsize kv) (vsize bv)
                                        (string_of_ket k) (string_of_bra b)
                 )
          );
  if bm<>S_1 || km<>S_1 then 
    raise (Error (Printf.sprintf "bra*ket multiplication with non-unit modulus\n%s\n%s"
                                        (string_of_ket k) (string_of_bra b)
                 )
          );
  maybe_sparse_m (init_m n n (fun i j -> cprod (?.kv i) (?.bv j)))
  
(* conjugate transpose: transpose and piecewise complex conjugate *)
let cconj_cv = List.map (fun (i,x) -> i, cconj x)

let dagger_m = function
  | SparseM (nc, cvv)        -> SparseM (nc, Array.map cconj_cv (transpose_cvv cvv))
  | DenseM dm as mA          -> let m = rsize mA in
                                let n = csize mA in
                                DenseM (init_m m n (fun i j -> cconj (dm.(j).(i))))
  | FuncM (id, rn, cn, f, opt) -> let id = Printf.sprintf "(%s)†" id in
                                FuncM (id, rn, cn, cconj <..> revargs f, opt &~~ (fun (rf, cf ) -> Some (cconj_cv <.> rf, cconj_cv <.> cf))) 

let dagger_g = dagger_m

let addsub_cvcv f s cvA cvB =
  let rec doit els cvA cvB =
    match cvA, cvB with
    | (i,x)::ixs, (j,y)::jys -> if i<j then doit ((i, f x   c_0)::els) ixs cvB else
                                if i=j then doit ((i, f x   y  )::els) ixs jys else
                                            doit ((j, f c_0 y  )::els) cvA jys
    | (i,x)::ixs, []         ->             doit ((i, f x   c_0)::els) ixs cvB
    | []        , (j,y)::jys ->             doit ((j, f c_0 y  )::els) cvA jys
    | []        , []         ->             List.rev els
  in
  doit [] cvA cvB
  
let addsub_ff f s f1 f2 i = addsub_cvcv f s (f1 i) (f2 i)

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
  | SparseM (_, cvvA)      , SparseM (_, cvvB)      -> 
      let cvv = Array.init m (fun i -> addsub_cvcv f s cvvA.(i) cvvB.(i)) in
      maybe_dense_m n cvv
  | FuncM (idA,_,_,fA,optA), FuncM (idB,_,_,fB,optB) -> 
      let id = Printf.sprintf "(%s)%s(%s)" idA s idB in
      let opt = match optA, optB with
                | Some (rfA,cfA), Some (rfB,cfB) -> Some (addsub_ff f s rfA rfB, addsub_ff f s cfA cfB)
                | _                              -> None
      in
      FuncM (id, m, n, (fun i j -> f (fA i j) (fB i j)), opt)
  | _                                                -> 
      maybe_sparse_m (init_m m n (fun i j -> f (?..mA i j) (?..mB i j)))

let add_mm = addsub_mm csum "+"
let sub_mm = addsub_mm cdiff "-"

let engate mA =
  let m = rsize mA in
  let n = csize mA in
  if m<>n then raise (Error (Printf.sprintf "non-square engate %s" (string_of_matrix mA)));
  (try ignore (log_2 m) 
   with _ -> raise (Error (Printf.sprintf "matrix size %d is not power of 2 in engate %s" m (string_of_matrix mA)))
  );
  let mB = mult_mm mA (dagger_m mA) in
  if exists_m (fun i j x -> j=i && x<>c_1 || j<>i && x<>c_0) mB then
    raise (Error (Printf.sprintf "non-unitary engate %s\n(m*m† = %s)" (string_of_matrix mA) (string_of_matrix mB)));
  gate_of_matrix mA