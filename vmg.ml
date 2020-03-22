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
open Snum
open Forutils

exception Error of string
exception Disaster of string

(* *********************** vectors, matrices,gates ************************************ *)

(* snv: symbolic normalised vector *)
type snv = modulus * csnum array (* modulus, vector: written as 1/sqrt(modulus)(vec) *)

type gate = 
    | MGate of matrix              (* must be square *)
    | DGate of csnum array         (* diagonal matrix *)

and matrix = csnum array array     (* not necessarily square *)

let vsize = Array.length
let snvsize (_,v) = vsize v
let rsize = Array.length
let csize m = vsize m.(0)
let gsize = function
  | MGate m -> rsize m  (* assuming square gates *)
  | DGate v -> vsize v
  

let make_snv ss = S_1, Array.of_list ss

let minus  (C (x,y)) = (* only for local use, please *)
  let negate = function
    | S_0 -> S_0
    | s   -> S_neg s
  in
  C (negate x, negate y) 

let snv_zero  = make_snv [c_1   ; c_0         ]
let snv_one   = make_snv [c_0   ; c_1         ]
let snv_plus  = make_snv [c_h   ; c_h         ]
let snv_minus = make_snv [c_h   ; minus c_h   ]

let snv_1 = make_snv [c_1] (* a unit for folding *)
let snv_0 = make_snv [c_0] (* another unit for folding *)

type bksign = PVBra | PVKet

let string_of_snv bksign = 
  let so_snv v =
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
         | _           -> false
       in
       let estrings = _for_leftfold 0 1 n
                        (fun i ss -> match string_of_csnum v.(i) with
                                     | "0"  -> ss
                                     | "1"  -> (string_of_basis_idx i) :: ss
                                     | "-1" -> ("-" ^ string_of_basis_idx i) :: ss
                                     | s   ->  (Printf.sprintf "%s%s" 
                                                               (if mustbracket v.(i) then "(" ^s ^ ")" else s) 
                                                               (string_of_basis_idx i)
                                               ) :: ss
                        )
                        []
       in
       match estrings with
       | []  -> "??empty snv??"
       | [e] -> e
       | _   -> Printf.sprintf "(%s)" (sum_separate (List.rev estrings))
      )
    else
      (let estrings = Array.fold_right (fun s ss -> string_of_csnum s::ss) v [] in
       Printf.sprintf "(%s)" (String.concat " <,> " estrings)
      )
  in
  function
  | S_1, vv -> so_snv vv
  | vm , vv -> Printf.sprintf "<<%s>>%s" (string_of_snum vm) (so_snv vv)
  
let string_of_bra = string_of_snv PVBra
let string_of_ket = string_of_snv PVKet

let string_of_matrix m = 
  let strings_of_row r = Array.fold_right (fun s ss -> string_of_csnum s::ss) r [] in
  let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
  let rwidth r = List.fold_left max 0 (List.map String.length r) in
  let width = List.fold_left max 0 (List.map rwidth block) in
  let pad s = s ^ String.make (width - String.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}\n" block
  
let string_of_gate = function 
  | MGate m -> string_of_matrix m
  | DGate v -> "diag{" ^ string_of_list string_of_csnum " " (Array.to_list v) ^ "}"

let make_m rows = rows |> (List.map Array.of_list) |> (Array.of_list)

let matrix_of_gate = function
  | MGate m -> m
  | DGate v -> let n = vsize v in
               let zs = Listutils.tabulate n (const c_0) in
               let rows = Listutils.tabulate n (const zs) in
               let m = make_m rows in
               for i = 0 to n-1 do
                 m.(i).(i) <- v.(i)
               done;
               m

(* this should only be used if it's really a unitary matrix *)               
let gate_of_matrix m =
  let n = rsize m in
  let isdiag = _for_all 0 1 n (fun i ->
                               let row = m.(i) in
                               _for_all 0 1 n (fun j -> i=j || row.(j)=c_0)
                              )
  in
  if isdiag then
    DGate (Array.init n (fun i -> m.(i).(i)))
  else MGate m
  
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
  make_g  [[c_1; c_0; c_0      ; c_0       ];
           [c_0; c_1; c_0      ; c_0       ];
           [c_0; c_0; m.(0).(0); m.(0).(1) ];
           [c_0; c_0; m.(1).(0); m.(1).(1) ]]
    
let g_CX   = make_C g_X
let g_CY   = make_C g_Y
let g_CZ   = make_C g_Z 
let g_Cnot = g_CX
                      
let g_1 = make_g [[c_1]] (* a unit for folding *)
let g_0 = make_g [[c_0]] (* another unit for folding, maybe *)

let m_1 = make_m [[c_1]]
let m_0 = make_m [[c_0]]

(* the special Grover gate. Oh this is a filthy hack. *)
let groverG n =
  if n<1 || n>=20 then raise (Error (Printf.sprintf "grovergate %d" n)) else
  (let s = S_h (2*(n-1)) in
   let cp = csnum_of_snum s in
   let size = 1 lsl n in
   let row _ = Array.init size (fun _ -> cp) in
   let m = Array.init size row in
   let s' = cdiff cp c_1 in
   for i=0 to size-1 do
     m.(i).(i) <- s'
   done;
   gate_of_matrix m
  )
  
let groverU bs =
  let ns = List.map (fun b -> if b then 1 else 0) bs in
  let size = 1 lsl (List.length ns) in
  let rec address r ns =
    match ns with
    | n::ns -> address (2*r+n) ns
    | []    -> r
  in
  let k = address 0 ns in
  let row i = Array.init size (fun j -> if i=j then
                                          (if j=k then cneg c_1 else c_1)
                                        else c_0
                              ) 
  in
  let m = Array.init size row in
  gate_of_matrix m



(* ******************* gate, matrix, vector arithmetic ****************************)

(* note that gates are square matrices, but we also have unsquare matrices *)

let init_v n f = Array.init n f
let init_m n m f = Array.init m (fun i -> Array.init m (f i))

let exists_v p v = _for_exists 0 1 (vsize v) (fun i -> p i v.(i))
let exists_m p m = exists_v (fun i row -> exists_v (fun j x -> p i j x) row) m

let tensor_vv vA vB =
  let nA = vsize vA in
  let nB = vsize vB in
  let vR = init_v (nA*nB) (fun i -> c_0) in
  for i = 0 to nA-1 do 
    for j = 0 to nB-1 do vR.(i*nB+j) <- cprod vA.(i) vB.(j)
    done
  done;
  vR

let tensor_pv2 (mA,vA) (mB,vB) = (rprod mA mB, tensor_vv vA vB)
  
let tensor_qq (mA,vA as pvA) (mB,vB as pvB) =
  let mR, vR = tensor_pv2 pvA pvB in
  if !verbose_qcalc then Printf.printf "%s ⊗ %s -> %s\n"
                                       (string_of_ket (mA,vA))
                                       (string_of_ket (mB,vB))
                                       (string_of_ket (mR,vR));
  mR,vR

let tensor_mm mA mB =
  let rA, cA = rsize mA, csize mA in
  let rB, cB = rsize mB, csize mB in
  let mC = init_m (rA*rB) (cA*cB) (fun _ _ -> c_0) in
  for i = 0 to rA-1 do
    for j = 0 to cA-1 do
      let aij = mA.(i).(j) in
      for m = 0 to rB-1 do
        for p = 0 to cB-1 do
          mC.(i*rB+m).(j*cB+p) <- cprod aij mB.(m).(p)
        done (* p *)
      done (* n *)
    done (* j *)
  done (* i *);
  mC
  
let tensor_gg gA gB =
  if !verbose_qcalc then Printf.printf "tensor_gg %s %s = " (string_of_gate gA) (string_of_gate gB);
  let g = if gA=g_1 then gB else
          if gB=g_1 then gA else
            (match gA, gB with
             | DGate dA, DGate dB -> DGate (tensor_vv dA dB)
             | _                  ->
                 let mA = matrix_of_gate gA in
                 let mB = matrix_of_gate gB in
                 let mC = tensor_mm mA mB in
                 gate_of_matrix mC
            )  
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_gate g);
  g

let fpow f one v n =
  List.fold_left f one (Listutils.tabulate n (const v))

let tensorpow_g = fpow tensor_gg g_1 
let tensorpow_snv = fpow tensor_pv2 snv_1
let tensorpow_m = fpow tensor_mm m_1
  
let rowcolprod n row col =
  let de_C (C (x,y)) = x,y in
  let els = Listutils.tabulate n (fun j -> de_C (cprod (row j) (col j))) in
  let reals, ims = List.split els in
  C (simplify_sum (sflatten reals), simplify_sum (sflatten ims))  

let mult_gv g (vm,vv as v) =
  if !verbose_qcalc then Printf.printf "mult_gv %s %s = " (string_of_gate g) (string_of_ket v);
  let n = Array.length vv in
  if gsize g <> n then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_gv %s %s"
                                 (string_of_gate g)
                                 (string_of_ket v)
                 )
          );
  let v' = vm, match g with
               | MGate m -> Array.init n (fun i -> let row = m.(i) in rowcolprod n (fun j -> row.(j)) (fun j -> vv.(j)))
               | DGate d -> Array.init n (fun i -> cprod d.(i) vv.(i))
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_ket v');
  v'

let mult_mm mA mB = 
  let m = rsize mA in
  let n = csize mA in
  if n<>rsize mB then
    raise (Error (Printf.sprintf "matrix size mismatch in multiply: %s * %s"
                                 (string_of_matrix mA)
                                 (string_of_matrix mB)
                 )
          );
  let p = csize mB in
  init_m m p (fun i j -> let row = mA.(i) in rowcolprod n (fun k -> row.(k)) (fun k -> mB.(k).(j)))
  
let mult_gg gA gB = 
  if !verbose_qcalc then Printf.printf "mult_gg %s %s = " (string_of_gate gA) (string_of_gate gB);
  let n = gsize gA in
  if n <> gsize gB then (* our gates are square *)
    raise (Error (Printf.sprintf "gate size mismatch in multiply: %s * %s"
                                 (string_of_gate gA)
                                 (string_of_gate gB)
                 )
          );
  let g = match gA, gB with
          | DGate dA, DGate dB -> DGate (Array.init n (fun i -> cprod dA.(i) dB.(i)))
          | _                  -> 
              let mA = matrix_of_gate gA in   
              let mB = matrix_of_gate gB in
              let m' = mult_mm mA mB in
              gate_of_matrix m' 
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_gate g);
  g

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
  init_m n n (fun i j -> cprod kv.(i) bv.(j))
  
(* conjugate transpose: transpose and piecewise complex conjugate *)
let dagger_m mA = 
  let m = rsize mA in
  let n = csize mA in
  init_m m n (fun i j -> cconj mA.(j).(i))
  
let dagger_g g = 
  if !verbose_qcalc then Printf.printf "dagger %s = " (string_of_gate g);
  let n = gsize g in
  let g' = match g with
           | DGate d -> DGate (Array.init n (fun i -> cconj d.(i)))
           | MGate m -> MGate (dagger_m m)
  in
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_gate g');
  g'
  
let addsub_mm f s mA mB =
  let m = rsize mA in
  let n = csize mA in
  if m<>rsize mB || n<>csize mB then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): %s %s %s"
                                 s
                                 (string_of_matrix mA)
                                 (string_of_matrix mB)
                 )
          );
  init_m m n (fun i j -> f mA.(i).(j) mB.(i).(j))

let add_mm = addsub_mm csum "add_mm"
let sub_mm = addsub_mm cdiff "sub_mm"

let engate mA =
  let m = rsize mA in
  let n = csize mA in
  if m<>n then raise (Error (Printf.sprintf "non-square engate %s" (string_of_matrix mA)));
  let rec is_twopower i =
    i=1 || i<>0 && i land 1=0 && is_twopower (i lsr 1)
  in
  if not (is_twopower m) then
    raise (Error (Printf.sprintf "matrix size %d is not power of 2 in engate %s" m (string_of_matrix mA)));
  let mB = mult_mm mA (dagger_m mA) in
  if exists_m (fun i j x -> j=i && x<>c_1 || j<>i && x<>c_0) mB then
    raise (Error (Printf.sprintf "non-unitary engate %s\n(m*m† = %s)" (string_of_matrix mA) (string_of_matrix mB)));
  gate_of_matrix mA