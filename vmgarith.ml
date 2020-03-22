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
open Value
open Forutils

exception Error of string

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
let tensorpow_snv = fpow tensor_pv2 pv_1
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