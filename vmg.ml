(*
    Copyright (C) 2020 Richard Bornat
     
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
  
let stats_ref table cn = try CsnumHash.find table cn 
                         with _ -> (let r = ref z_0 in CsnumHash.add table cn r; r)

let stats_inc table inc cn = 
  let r = stats_ref table cn in
  r:=!r+:inc

let stats_to_list table =
  let compare (i,fi) (j,fj) = ~-(Z.compare fi fj) in
  List.sort compare (List.map (fun (v,r) -> v,!r) (CsnumHash.to_assoc table))
  
(* *********************** vectors, matrices,gates ************************************ *)

(* because matrices and vectors can become very large (see the W example), indices are now zint *)
(* because Arrays can't get that large, they are indexed by ints. Ho hum. 
   But an Array would be too big for memory long before it ran out of indices.
 *)
(* and actually a SparseM is an array of cvecs, so it has to be indexed by int. Ho hum again. 
   Sparse matrices can reasonably be larger than the int address space, and we deal with 
   2^1024 examples in the W state example. But that's done with functional matrices. The
   time optimisations I developed need an explicit sparse matrix representation. So there.
 *)

type dvec  = csnum array
and  cvec  = (zint * csnum) list                (* assoc list *)

type vector = 
  | DenseV   of dvec                            (* always 2^n-sized, but we don't have existential type for that *)
  | SparseV  of zint * csnum * cvec             (* size, default value, values *)

and matrix = 
  | DenseM of dmat                              (* not necessarily square *)
  | SparseM of zint * csnum * cvec array        (* csize, default value, sparse rows *)
  | FuncM  of string * zint * zint * (zint -> zint -> csnum) * (csnum * (zint -> cvec) * (zint -> cvec)) option
                                                (* rsize, csize, element function, sparse row/column option *)
  | DiagM of vector                             (* rsize=csize=diagsize *)

and dmat = csnum array array

and nv = modulus * vector                       (* modulus, vector: meaning 1/sqrt(modulus)(vec) *)

and modulus = snum 

and gate = matrix                               (* gates must be square, unitary and 2^n-sized, 
                                                   but to say that we would need an existential type.
                                                 *)

let showdmat m =
  let nr, nc = Array.length m, if Array.length m = 0 then 0 else Array.length m.(0) in
  let block = tabulate nr (fun r -> tabulate nc (fun c -> string_of_csnum m.(r).(c))) in
  let maxwidth row = List.fold_left max 0 (List.map Utf8.length row) in
  let maxwidth = List.fold_left max 0 (List.map maxwidth block) in 
  let pad s = s^ String.make (maxwidth - Utf8.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}\n" block

module DmatH = struct type t = dmat 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = showdmat
               end
module DMatHash = MyHash.Make (DmatH)
                    
module DmatH2 = struct type t = dmat*dmat 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string (m1,m2) =  "(" ^ showdmat m1 ^ "," ^ showdmat m2 ^ ")"
                  end

module DMatHash2 = MyHash.Make (DmatH2)

let string_of_cv assoc = Printf.sprintf "[%s]" (string_of_assoc string_of_zint string_of_csnum ":" ";" assoc)

let vsize = function
  | DenseV  v       -> Z.of_int (Array.length v)
  | SparseV (n,_,_) -> n

let nvsize (_,v) = vsize v
        
let rsize = function
  | DenseM m                -> Z.of_int (Array.length m)
  | SparseM (nc, sv, cvs)   -> Z.of_int (Array.length cvs)
  | FuncM  (_,nr,_,_,_)     -> nr
  | DiagM   v               -> vsize v

let csize = function
  | DenseM m                -> if Array.length m = 0 then z_0 else Z.of_int (Array.length m.(0))
  | SparseM (nc, sv, cvs)   -> nc
  | FuncM  (_,_,nc,_,_)     -> nc
  | DiagM   v               -> vsize v

let gsize = rsize

let init_v n f = Array.init n f
let init_dm n m f = Array.init m (fun i -> Array.init m (f i))

(* cvecs are ordered ... *)

let cvel_compare (i,_) (j,_) = ~-(Z.compare i j)

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
  | DiagM   v               -> if i=:j then ?.v i else c_0

(* a bit of false recursion, so I don't have to find what order to put these functions in 
   -- all so I can use string_of_vector in diag printing when I need to
 *)
type bksign = PVBra | PVKet

let rec densify_cv n sv cv = Array.init (my_to_int n "densify_cv") (find_cv sv cv <.> Z.of_int)

and densify_v = function
  | DenseV  v         -> v
  | SparseV (n,sv,cv) -> densify_cv n sv cv

(* fold_left_v would be an impressive thing. For the time being, I shy away, and build sum_v to sum amplitudes *)  
and sum_v  = function
  | DenseV  v         -> Array.fold_left csum c_0 v
  | SparseV (n,sv,cv) -> csum (cprod_r sv (snum_of_zint (n-:Z.of_int (List.length cv))))
                              (List.fold_left (fun acc (_,n) -> csum acc n) c_0 cv)
                              
and dense_countzeros_v n m v :int = (* from n to m-1, natch *)
  _for_fold_left n 1 m 0 (fun nzs i -> if v.(i)=c_0 then nzs+1 else nzs)
  
and countzeros_v n m v :zint = (* from n to m-1, natch *)
  if n>=:m then z_0 else match v with
                         | DenseV  v                     -> Z.of_int (dense_countzeros_v (Z.to_int n) (Z.to_int m) v)
                         | SparseV (_,sv,cv) when sv=c_0 -> let cv' = cvseg n m cv in Z.(m-n-Z.of_int (List.length cv'))
                         | SparseV (nc,sv,cv)            -> 
                             Z.(List.fold_left (fun nz (_,x) -> if x=c_0 then nz+z_1 else nz) z_0 cv)

and samehalves_v v :bool = (* are the two halves of the vector the same? Used in try_split *)
  let nv = vsize v in
  let nh = nv /: z_2 in
  match v with
  | DenseV  v         -> let nh = Z.to_int nh in
                         _for_all 0 1 nh (fun i -> v.(i)=v.(i+nh))
  | SparseV (_,sv,cv) -> let cvl, cvh = takedropwhile (fun (i,_) -> i<:nh) cv in
                         (try List.for_all (fun ((i,vl),(j,vh)) -> Z.(i+nh=j) && vl=vh) (zip cvl cvh)
                          with Zip -> false
                         )

and sameneghalves_v v :bool = (* is the top half the negated bottom half? Used in try_split *)
  let nv = vsize v in
  let nh = nv /: z_2 in
  match v with
  | DenseV  v         -> let nh = Z.to_int nh in
                         _for_all 0 1 nh (fun i -> v.(i)=cneg (v.(i+nh)))
  | SparseV (_,sv,cv) -> sv=c_0 && (* it's effectively impossible with non-zero sv *)
                         let cvl, cvh = takedropwhile (fun (i,_) -> i<:nh) cv in
                         (try List.for_all (fun ((i,l),(j,h)) -> Z.(i+nh=j) && l=cneg h) (zip cvl cvh)
                          with Zip -> false
                         )

and cv_of_dv sv dv = 
  let nxs = Array.to_list (Array.mapi (fun i x -> (Z.of_int i),x) dv) in
  List.filter (fun (_,x) -> x<>sv) nxs

and svfreq_v v =
  let stats = statistics_v v in List.hd stats

(* we have algorithms that are faster for sparse vectors, so we do them no matter how small *)  
and maybe_sparse_v dv =
  let v = DenseV dv in
     (let sv,freq = svfreq_v v in
      let n = Z.of_int (Array.length dv) in
      if Z.(freq*z_4>z_3*n) then SparseV (n, sv, cv_of_dv sv dv)
                            else v
    )

and dv_of_cv sv (n:zint) cv =
  let dv = Array.make (my_to_int n "dv_of_cv 1") sv in
  List.iter (fun (i,x) -> dv.(my_to_int i "dv_of_cv 2") <- x) cv;
  dv

and maybe_dense_v sv n cv =
  let dense () = DenseV (dv_of_cv sv n cv) in
  if n>:z_4 then
    (let vv = SparseV (n, sv, cv) in
     if Z.(of_int (List.length cv)*z_4<=n) then vv 
     else
       let stats = statistics_v vv in
       let sv',freq = List.hd stats in
       if Z.(freq*z_4>z_3*n) then
         if sv=sv' then vv 
                   else SparseV (n,sv',sparse_elements_cv sv sv' n cv) 
       else (if !verbose || !verbose_qcalc then
               Printf.printf "maybe_dense_v %s dense with n=%s sv=%s stats=[\n%s]\n" 
                    (string_of_vector vv)
                    (string_of_zint n) 
                    (string_of_csnum sv) 
                    (string_of_assoc string_of_csnum string_of_zint ":" ";\n" stats);
             dense()
            )
    )
  else dense()

and sparse_elements_cv sv sv' n cv = (* fill in all the gaps with sv, cut out all the sv's *)
  if sv=sv' then cv else
    (let rec svs k n ixs =
       if k=:n then ixs else svs (k+:z_1) n ((k,sv)::ixs) 
     in
     let rec f ixs k = function
       | []              -> List.rev (svs k n ixs)
       | (i,x as ix)::cv -> let ixs = svs k i ixs in
                            f (if x=sv' then ixs else ix::ixs) (i+:z_1) cv
     in 
     f [] z_0 cv
    )
                   
and sparse_elements_dv sv dv = List.filter (fun (_,x) -> x<>sv) (Array.to_list (Array.mapi (fun i x -> Z.of_int i,x) dv))

and sparse_elements_v sv vV =
  match vV with
  | SparseV (n,sv',cv) -> if sv=sv' then cv 
                          else sparse_elements_cv sv sv' n cv
  | DenseV  v          -> sparse_elements_dv sv v

and sparse_of_diag v =
  let doit n v = SparseM (n, c_0, Array.init (Z.to_int n) (fun i -> [(Z.of_int i,v.(i))])) in
  match v with
  | SparseV (n,_,_) -> doit n (densify_v v)
  | DenseV  dv      -> doit (Z.of_int (Array.length dv)) dv
  
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
 
and string_of_nv bksign (vm, vv) = 
  let so_v m v =
    if !Settings.fancyvec then 
      (let n = vsize v in
       let width = log_2 n in
       let string_of_bin i =
         let rec sb i k =
           if k=width then ""
           else sb Z.(i/z_2) (k+1) ^ if Z.(i mod z_2 = z_0) then "0" else "1"
         in
         sb i 0
       in
       let string_of_basis_idx i =
         Printf.sprintf (match bksign with PVBra -> "⟨%s|" | PVKet -> "|%s⟩") (string_of_bin i)
       in
       let is_single = countzeros_v z_0 n v = Z.(n-one) in
       let tracediv = false in
       let gcd = 
         if is_single || not !factorbraket then sprod_1
         else (* we're going to find the num which is sort of gcd of everything *)
              (let amps = match v with (* we just need a list, not frequencies *)
                 | DenseV  v         -> Array.to_list v
                 | SparseV (n,sv,cv) -> sv::(List.map snd cv)
               in
               let amps = List.filter (fun c -> c<>c_0) amps in
               let rec common_els gels els1 els2 =
                 match els1, els2 with
                 | [], _
                 | _ , [] -> List.rev gels
                 | el1::tail1, el2::tail2 ->
                    match Snum.elcompare el1 el2 with
                    |  -1 -> common_els gels tail1 els2
                    | 0   -> common_els (el1::gels) tail1 tail2
                    | _   -> common_els gels els1 tail2
               in
               let gcd_prod gcd (num,els as prod) = 
                 match gcd with
                 | None              -> Some prod
                 | Some (gnum, gels) -> Some (Number.gcd gnum num, common_els [] gels els)
               in
               let gcd_num gcd prods = List.fold_left gcd_prod gcd prods in
               let n = List.fold_left (fun gcd (C (r,i)) -> gcd_num (gcd_num gcd i) r)
                                      None
                                      amps
               in
               if tracediv then Printf.printf "gcd is %s\n" (string_of_option string_of_sprod n); 
               if n=None || is_single then sprod_1 else _The n
             )
         in
         (* it's important, with sparse vectors, not to scan one element at a time ... *)
         let v_els =
           let mingap i j = Z.(j-i>=z_4) in
           let n = vsize v in
           match v with
           | DenseV _          ->
               let rec nxf ves i = 
                  if i=:n then ves (* reversed later *)
                  else
                    let amp = ?.v i in
                    if amp=c_0 then nxf ves Z.(i+one) 
                    else
                      let rec tw j = if Z.(j<n) && ?.v j=amp then tw Z.(j+one) else j in
                      let j = tw Z.(i+one) in
                      if not !runbraket || not (mingap i j) then nxf ((i,amp,Z.one)::ves) Z.(i+one)
                                                            else nxf ((i,amp,j-:i)::ves)  j
               in
               nxf [] Z.zero
           | SparseV (n,sv,cv) ->
               let rec nxf cv ves i =
                 match cv with
                 | (j,amp)::cv' ->
                     if amp=c_0 then nxf cv' ves Z.(i+one)
                     else
                     if i<:j then 
                       (if sv=c_0 then nxf cv ves j 
                        else
                          if not !runbraket || not (mingap i j) then nxf cv ((i,sv,Z.one)::ves) Z.(i+one) 
                                                                else nxf cv ((i,sv,j-:i)::ves)  j 
                       ) 
                     else (* i=:j assumed ... *)
                       let rec tw cv j =
                         match cv with
                         | (j',amp')::cv' when Z.(j=j') && amp=amp' -> tw cv' Z.(j'+one)
                         | _                                        -> cv, j
                       in
                       let cv'', j = tw cv' Z.(i+one) in
                       if not !runbraket || not (mingap i j) then nxf cv'  ((i,amp,Z.one)::ves)   Z.(i+one) 
                                                             else nxf cv'' ((i,amp,Z.(j-i))::ves) j 
                | [] -> 
                    if i=:n || sv=c_0 then ves (* reversed later *) 
                    else
                      if not !runbraket || not (mingap i n) then nxf cv ((i,sv,Z.one)::ves)   Z.(i+one) 
                                                            else nxf cv ((i,sv,Z.(n-i))::ves) n
              in 
              nxf cv [] Z.zero
         in
       let estrings_rev =
         let coeff x = 
           (* here's where we employ gcd *)
           let rec coeff_els rels gels els =
             match gels, els with
             | [], _
             | _ , []                -> Listutils.prepend rels els
             | gel::gtail, el::etail ->
                if gel=el then coeff_els rels gtail etail
                          else coeff_els (el::rels) gels etail
           in
           let coeff_prod (num, els) = 
             num//fst gcd, coeff_els [] (snd gcd) els
           in
           let coeff_num = List.map coeff_prod in
           let coeff_csnum (C (r,i)) = C (coeff_num r, coeff_num i) in
           match so_csnumb true (coeff_csnum x) with
           | "1"  -> ""
           | "-1" -> "-"
           | s    -> s
         in
         let estringf i amp = coeff amp ^ string_of_basis_idx i in
         List.map (fun (i,amp,gap) ->
                     if Z.(gap=one) then estringf i amp
                     else
                       let isneg = not (coeff amp="") && Stringutils.first (coeff amp)='-' in
                       estringf i amp ^
                       (if isneg then "-" else "+") ^ "..." ^ (if not isneg then "+" else "") ^
                       estringf Z.(i+gap-one) amp
                  )
                  v_els
       in
       let pre = rprod m [gcd] in
       match estrings_rev with 
       | []                   -> "?..empty nv?.."
       | [e] when pre=snum_1  -> e 
       | _                    -> Printf.sprintf "%s(%s)" (if pre=snum_1 then "" else string_of_snum pre) (sum_separate (List.rev estrings_rev))
      )
    else
      raw_string_of_vector v
  in
  (* since splitting the state is now not a normal thing, we don't need this ...
     let normalised_sign vv = 
       let doit x = 
         try match (string_of_csnum x).[0] with
             | '-' -> so_v (map_v cneg vv)
             | _   -> so_v vv 
         with exn -> Printf.eprintf "doit got it\n"; flush_all(); raise exn
       in
       match vv with
       | SparseV (_, sv, (i,x)::_) -> if sv=c_0 || i=z_0 then doit x else doit sv
       | SparseV (n, sv, []      ) -> doit sv
       | DenseV  v                 -> let xs = dropwhile ((=) c_0) (Array.to_list v) in
                                      match xs with
                                      | x::xs -> doit x
                                      | []    -> so_v vv
     in
   *)
  let vmultiplier () =
    match vm with
    | [(n,[])] -> (match exactsqrt n with
                   | Some root -> so_v [reciprocal root,[]] vv
                   | None      -> match zint_exactsqrt n.den, zint_exactsqrt n.num with
                                  | Some denroot, _ -> Printf.sprintf "%s/√(%s)(%s)" (string_of_zint denroot) (string_of_zint n.num) (so_v snum_1 vv)
                                  | _, Some numroot -> Printf.sprintf "√(%s)/%s(%s)" (string_of_zint n.den) (string_of_zint numroot) (so_v snum_1 vv)
                                  | _               -> Printf.sprintf "√(%s)(%s)" (string_of_num (reciprocal n)) (so_v snum_1 vv)
                  )
    | _        -> Printf.sprintf "<<modulus %s>>%s" (string_of_snum vm) (so_v snum_1 vv)
  in
  if vm=snum_1 then so_v vm vv else vmultiplier ()
  
and string_of_bra b = string_of_nv PVBra b
and string_of_ket k = string_of_nv PVKet k

and string_of_vector v = string_of_ket (snum_1,v)

and raw_string_of_vector v = 
  match v with
  | DenseV  v         -> let estrings = Array.fold_right (fun s ss -> string_of_csnum s::ss) v [] in
                         Printf.sprintf "DenseV%s" (bracketed_string_of_list id estrings)
  | SparseV (n,sv,cv) -> Printf.sprintf "SparseV(%s,%s,%s)" (string_of_zint n) (string_of_csnum sv) (string_of_cv cv)


(* with sparse vectors, we can have some seriously large ones ... *)
and stats_vc count v = 
  match v with
  | DenseV  dv        -> let stats = CsnumHash.create (max 1000 (Array.length dv*4)) in
                         Array.iter (count stats) dv;
                         stats
  | SparseV (n,sv,cv) -> let stats = CsnumHash.create (max 1000 (List.length cv*4)) in
                         stats_inc stats (n-:zlength cv) sv;
                         List.iter (count stats <.> snd) cv;
                         stats

and stats_v v = stats_vc (fun stats x -> stats_inc stats z_1 x) v
  
and statistics_v v :(csnum*zint) list =
  stats_to_list (stats_v v)

(* had to promote these because string_of_vector uses div_nv *)
and mult_nv cn v =
  if cn=c_0 then SparseV (vsize v, c_0, []) else
  if cn=c_1 then v                          else
    match v with 
    | DenseV  v         -> DenseV (Array.map (fun x -> cprod cn x) v)
    | SparseV (n,sv,cv) -> SparseV (n, cprod cn sv, List.map (fun (i,x) -> i, cprod cn x) cv)

and mult_snv sn v = mult_nv (csnum_of_snum sn) v

and div_nv cn v =
  if cn=c_0 then raise (Disaster "div_nv can't divide by c_0") else
  if cn=c_1 then v                                             else
    match v with 
    | DenseV  v         -> DenseV (Array.map (fun x -> cdiv x cn) v)
    | SparseV (n,sv,cv) -> SparseV (n, cdiv sv cn, List.map (fun (i,x) -> i, cdiv x cn) cv)

and div_snv sn v = div_nv (csnum_of_snum sn) v


let statistics_nv (_,v) = statistics_v v

let string_of_cvv cvv = bracketed_string_of_list string_of_cv (Array.to_list cvv)

exception NotDiag

let diagcv_of_cvv cvv =
  _for_fold_right 0 1 (Array.length cvv)
                  (fun i es -> match cvv.(i) with
                               | [(zj,_) as e] -> if Z.of_int i=:zj then e::es else raise NotDiag
                               | []            -> es
                               | _             -> raise NotDiag
                  )
                  []

let string_of_matrix m = 
  let showdense () =
    let nr, nc = Z.to_int (rsize m), Z.to_int (csize m) in
    let block = tabulate nr (fun r -> tabulate nc (fun c -> string_of_csnum (?..m (Z.of_int r) (Z.of_int c)))) in
    let maxwidth row = List.fold_left max 0 (List.map Utf8.length row) in
    let maxwidth = List.fold_left max 0 (List.map maxwidth block) in 
    let pad s = s^ String.make (maxwidth - Utf8.length s) ' ' in
    let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
    Printf.sprintf "\n{%s}\n" block
  in 
  if !showdensematrices then
    showdense ()
  else
    match m with
    | DenseM m -> showdense ()
    | SparseM (nc,sv,cvv) ->  
        (* could be sparse diagonal *)
        (try let cv = diagcv_of_cvv cvv in
             Printf.sprintf "SparseDiagM(%s,%s,%s)\n" (string_of_zint nc) (string_of_csnum sv) 
                                                      (raw_string_of_vector (maybe_dense_v sv nc cv))
         with NotDiag ->
           Printf.sprintf "SparseM %s %s %s\n" (string_of_zint nc) (string_of_csnum sv) (string_of_cvv cvv)
        )
    | FuncM (id,nr,nc,_,opt) ->
        Printf.sprintf "FuncM(%s,%s,%s,_,%s)" id (string_of_zint nr) (string_of_zint nc) 
                                              (Optionutils.string_of_option (fun (sv,_,_) -> Printf.sprintf "%s,_,_" (string_of_csnum sv)) 
                                                                            opt
                                              )
    | DiagM v -> Printf.sprintf "DiagM(%s)" (raw_string_of_vector v)
  
let string_of_gate = string_of_matrix

let statistics_m m :(csnum*zint) list =
  let count stats = stats_inc stats z_1 in
  let stats = match m with
              | DenseM  dm          -> let stats = CsnumHash.create (min 1000 (Array.length dm * Array.length dm.(0) * 4)) in
                                       Array.iter (Array.iter (count stats)) dm;
                                       stats
              | SparseM (nc,sv,cvv) -> let size = Array.fold_left (fun accum cv -> accum+List.length cv) 0 cvv in
                                       let stats = CsnumHash.create (min 1000 (size*4)) in
                                       let svr = stats_ref stats sv in
                                       let count_cv cv = 
                                         svr :=!svr+:nc-:zlength cv;
                                         List.iter (count stats <.> snd) cv
                                       in
                                       Array.iter count_cv cvv;
                                       stats
              | FuncM (_,nr,nc,f,_) -> (* this is a stupid question: hope nobody ever asks ... *)
                                       let stats = CsnumHash.create 10000 in
                                       _forZ z_0 z_1 nr (fun i ->
                                         _forZ z_0 z_1 nc (fun j -> count stats (f i j))
                                       );
                                       stats
              | DiagM   v           -> let stats = stats_v v in
                                       let s0 = stats_ref stats c_0 in
                                       let vn = vsize v in
                                       s0 := !s0 +: (vn *: vn) -: vn;
                                       stats
  in
  stats_to_list stats

let countzeros_dm dm :int = 
  Array.fold_left (Array.fold_left (fun n x -> if x=c_0 then n+1 else n)) 0 dm

let cvv_of_dm sv = Array.map (cv_of_dv sv)

let svfreq_m m =  
  let stats = statistics_m m in
  List.hd stats

let trace_diag = true

let maybe_diag_m nr nc sv cvv =
   if trace_diag && (!verbose || !verbose_qcalc) then 
     Printf.printf "maybe_diag_m %s %s %s %s" (Z.to_string nr) (Z.to_string nc) (string_of_csnum sv) (string_of_cvv cvv);
   let r = try if not !trydiag || nr<>nc || sv<>c_0 then raise NotDiag;
               let cv = diagcv_of_cvv cvv in
               DiagM (maybe_dense_v sv nr cv)
           with NotDiag -> SparseM (nc, sv, cvv)
   in
   if trace_diag && (!verbose || !verbose_qcalc) then Printf.printf " = %s\n" (string_of_matrix r);
   r
   
let init_diag_m : zint -> (zint -> csnum) -> matrix = fun n f ->
  (* let r = *) 
  if !trydiag then DiagM (maybe_sparse_v (Array.init (Z.to_int n) (f <.> Z.of_int))) 
              else SparseM (n, c_0, Array.init (Z.to_int n) (fun i -> let zi = Z.of_int i in [zi, f zi]))
  (* in
  Printf.printf "init_diag_m %s ?? = %s\n" (Z.to_string n) (string_of_matrix r);
  r *)

let maybe_sparse_m dm =
  let m = DenseM dm in
  if rsize m>:z_4 then
    (let sv,freq = svfreq_m m in
     let nr, nc = rsize m, csize m in
     if Z.(freq*z_4 > z_3*nr*nc) then maybe_diag_m nr nc sv (cvv_of_dm sv dm)
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
       if sv=sv' then maybe_diag_m nr nc sv cvv
                 else maybe_diag_m nr nc sv' (Array.map (sparse_elements_cv sv sv' nc) cvv)
     else dense()
    )
  else dense()

(* I don't need this any more. Which means I didn't need to modularise PQueue. Oh well.  
   module OrderedPrioZ = struct type prio = zint
                               let compare = (~-)<..>Z.compare
                        end

   module Zpq = PQueue.Make (OrderedPrioZ)
 *)

module CvvH = struct type t = zint * cvec array 
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = bracketed_string_of_pair string_of_zint (bracketed_string_of_list string_of_cv <.> Array.to_list)
               end
module CvvHash = MyHash.Make (CvvH)

let cvvtab = CvvHash.create (100)

let transpose_cvv = 
  curry2 
    (CvvHash.memofun "transpose_cvv" cvvtab (uncurry2 (fun nc cvv ->
        let nc = my_to_int nc "transpose_cvv" in
        let rvv = Array.make nc [] in
        for i = Array.length cvv -1 downto 0 do
          let row = cvv.(i) in
          let i = Z.of_int i in
          List.iter (fun (j,x) -> let j = Z.to_int j in rvv.(j) <- (i,x)::rvv.(j)) row;
        done;
        rvv 
      ))
    )

let transpose_m m =
  match m with
  | SparseM (nc,sv,cvv) -> SparseM (rsize m, sv, transpose_cvv nc cvv)
  | DenseM  dm          -> let nr = Z.to_int (rsize m) in
                           let nc = Z.to_int (csize m) in
                           DenseM (init_dm nr nc (fun i j -> dm.(j).(i)))
  | FuncM (id, rn, cn, f, opt) 
                        -> let id = Printf.sprintf "(%s)*" id in
                           FuncM (id, cn, rn, revargs f, 
                                   opt &~~ (fun (sv, rf, cf) -> Some (sv, cf, rf))
                                 ) 
  | DiagM  _            -> m

let rcftab = DMatHash.create (100)

let rowfopt_dm = DMatHash.memofun "rowfopt_dm" rcftab (fun dm ->
                      let sv,_ = svfreq_m (DenseM dm) in
                      let cvv = cvv_of_dm sv dm in
                      sv, Array.get cvv <.> Z.to_int, Array.get (transpose_cvv (Z.of_int (Array.length dm.(0))) cvv) <.> Z.to_int 
                   )

let rowfopt_m = function
  | SparseM (n, sv, cvv)      -> Some (sv, Array.get cvv <.> Z.to_int, Array.get (transpose_cvv n cvv) <.> Z.to_int)
  | FuncM   (id,nr,nc,f,optf) -> optf
  | DenseM  dm                -> Some (rowfopt_dm dm) (* if we are asked, it's needed *) 
  | DiagM   v                 -> let f i = [(i,?.v i)] in
                                 Some (c_0, f, f)
                       
(* ********************** build vectors, matrices, gates ******************************* *)

let make_nv ss = snum_1, DenseV (Array.of_list ss)

let nv_zero  = make_nv [c_1   ; c_0         ]
let nv_one   = make_nv [c_0   ; c_1         ]
let nv_plus  = make_nv [c_h   ; c_h         ]
let nv_minus = make_nv [c_h   ; cneg c_h    ]

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
let g_Y  = make_g   [[c_0       ; cneg c_i   ];
                     [c_i       ; c_0        ]]
let g_Z  = make_g   [[c_1       ; c_0        ];
                     [c_0       ; cneg c_1   ]] 
let g_ZX = make_g   [[c_0       ; c_1        ];
                     [cneg c_1  ; c_0        ]] 
let g_H  = make_g   [[c_h       ; c_h        ];
                     [c_h       ; cneg (c_h) ]]
                     
(* these are rotations. argument is fraction of 𝝅 -- e.g. 1/4 means 𝝅/4 *)

let g_Rx n = make_g   [[C(snum_trig true n, snum_0)        ; C(snum_0, rneg (snum_trig false n))];
                       [C(snum_0, rneg (snum_trig false n)); C(snum_trig true n, snum_0)        ]]
                     
let g_Ry n = make_g   [[C(snum_trig true n, snum_0) ; C(rneg (snum_trig false n), snum_0)];
                       [C(snum_trig false n, snum_0); C(snum_trig true n, snum_0)        ]]
                     
let g_Rz n = make_g   [[C(snum_trig true ~-/n, snum_trig false ~-/n); c_0                                   ];
                       [c_0                                         ; C(snum_trig true n, snum_trig false n)]]

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
          
let g_Toffoli = (* tediously, sorry *) (* this is an and gate *)
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
  Z.(let sn = make_snum_h n in
     let negsn = rneg sn in
     let f i j = 
       C ((if Stdlib.(land) (popcount (i land j)) 1 = 1 then negsn else sn), snum_0)
     in
     let gsize = z_1 lsl n in
     FuncM ((Printf.sprintf "H⊗⊗%d" n), gsize, gsize, f, None)
   )
   
(* ******************* gate, matrix, vector arithmetic ****************************)

(* note that gates are square matrices, but we also have unsquare matrices *)

let exists_Array p v = _for_exists 0 1 (Array.length v) (fun i -> p (Z.of_int i) v.(i))

let all_Array p v = _for_all 0 1 (Array.length v) (fun i -> p (Z.of_int i) v.(i))

let exists_v p = function DenseV dv           -> exists_Array p dv
                |         SparseV (n, sv, cv) -> _for_existsZ z_0 z_1 n (fun i -> p i (find_cv sv cv i))

let exists_m p = function
  | DenseM m            -> exists_Array (fun i row -> exists_Array (fun j x -> p i j x) row) m
  | SparseM (nc,sv,cvv) -> exists_Array (fun i cv -> let row = SparseV (nc,sv,cv) in
                                                     _for_existsZ z_0 z_1 nc (fun j -> p i j (?.row j))
                                        ) cvv
  | FuncM (_,nr,nc,f,_) -> _for_existsZ z_0 z_1 nr (fun i -> _for_existsZ z_0 z_1 nc (fun j -> p i j (f i j)))
  | DiagM v             -> let n = vsize v in
                           _for_existsZ z_0 z_1 n (fun i -> _for_existsZ z_0 z_1 n (fun j -> p i j (if i=:j then ?.v i else c_0)))
  
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


let nv_of_braket bks = 
  let rec nv (rm,rv as r) =
    function 
    | bk::bks -> let (m1,v1) = match bk with
                           | Braket.BKZero  -> nv_zero
                           | Braket.BKOne   -> nv_one
                           | Braket.BKPlus  -> nv_plus
                           | Braket.BKMinus -> nv_minus
                 in nv (rprod rm m1, tensor_vv rv v1) bks
    | []      -> r
  in 
  nv nv_1 bks

let tensor_nvnv (mA,vA) (mB,vB) = (rprod mA mB, tensor_vv vA vB)
  
let tensor_qq (mA,vA as nvA) (mB,vB as nvB) =
  let mR, vR = tensor_nvnv nvA nvB in
  if !verbose || !verbose_qcalc then Printf.printf "%s ⊗ %s -> %s\n"
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
  
let tensor_dmdm ma mb =
  let nra = Array.length ma in
  let nca = if nra=0 then 0 else Array.length ma.(0) in
  let nrb = Array.length mb in
  let ncb = if nrb=0 then 0 else Array.length mb.(0) in
  let dmc = init_dm (nra*nrb) (nca*ncb) (fun _ _ -> c_0) in
  for i = 0 to nra-1 do
    for j = 0 to nca-1 do
      let aij = ma.(i).(j) in
      for m = 0 to nrb-1 do
        for p = 0 to ncb-1 do
          dmc.(i*nrb+m).(j*ncb+p) <- cprod aij mb.(m).(p)
        done (* p *)
      done (* n *)
    done (* j *)
  done (* i *);
  maybe_sparse_m dmc
  
let dmdmtab = DMatHash2.create (100)
let tensor_dmdm = 
  curry2 (DMatHash2.memofun "tensor_dmdm" dmdmtab (uncurry2 tensor_dmdm))

let rec tensor_mm mA mB =
  if !verbose || !verbose_qcalc then Printf.printf "tensor_mm %s %s = " (string_of_matrix mA) (string_of_matrix mB);
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
             | DiagM v1            , DiagM v2             -> DiagM (tensor_vv v1 v2)
             | DiagM v1            , _                    -> tensor_mm (sparse_of_diag v1) mB
             | _                   , DiagM v2             -> tensor_mm mA (sparse_of_diag v2)
             | DenseM  dma         , SparseM (_,svb,cvvb) -> let sva,_ = svfreq_m mA in
                                                             let cvva = cvv_of_dm sva dma in
                                                             tensor_sparse_mm nra nca sva cvva nrb ncb svb cvvb
             | DenseM  dma         , DenseM  dmb          -> tensor_dmdm dma dmb
            )  
  in
  if !verbose || !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix m);
  m

let tensor_gg = tensor_mm

let tensorpow_g g n = 
  if !verbose || !verbose_qcalc then
    Printf.printf "tensorpow_g %s %d = " (string_of_gate g) n;
  let r = if n=0 then                     g_1             else
          if n=1 then                     g               else
          if !func_matrices && g=g_I then func_I n        else
          if !func_matrices && g=g_H then func_H n        else
                                          List.fold_left tensor_gg g (tabulate (n-1) (const g))
  in
  if !verbose || !verbose_qcalc then
    Printf.printf "%s\n" (string_of_gate r);
  r
  
let tensorpow_nv nv n = 
  if !verbose || !verbose_qcalc then
    Printf.printf "tensorpow_nv %s %d = " (string_of_ket nv) n;
  let r = if n=0 then nv_1             else
          if n=1 then nv               else
                      List.fold_left tensor_nvnv nv (tabulate (n-1) (const nv))
  in
  if !verbose || !verbose_qcalc then
    Printf.printf "%s\n" (string_of_ket r);
  r

let tensorpow_m = tensorpow_g

(* elwise: element-wise combination of vectors and matrices *)

let track_elwise = true

(* this gives you a cv with sv = ee sva svb *)
let elwise_cvcv ee str sva cva svb cvb =
  if track_elwise && (!verbose || !verbose_qcalc) then 
       Printf.printf "elwise_cvcv %s %s %s %s %s = " str (string_of_csnum sva) (string_of_cv cva) 
                                                         (string_of_csnum svb) (string_of_cv cvb); 
  let sv = ee sva svb in
  let rec f vs cva cvb =
    let vadd k v = if v=sv then vs else (k,v)::vs in
    Z.(match cva, cvb with
       | (i,x)::ixs, (j,y)::jys -> if i<j then f (vadd i (ee x svb)) ixs cvb else
                                   if i=j then f (vadd i (ee x y  )) ixs jys else
                                               f (vadd j (ee sva y)) cva jys
       | (i,x)::ixs, []         ->             f (vadd i (ee x svb)) ixs cvb 
       | []        , (j,y)::jys ->             f (vadd j (ee sva y)) cva jys
       | _                      -> List.rev vs
     )
  in
  let cv = f [] cva cvb in
  if track_elwise && (!verbose || !verbose_qcalc) then Printf.printf "%s, %s\n" (string_of_csnum sv) (string_of_cv cv); 
  sv, cv

let elwise_dvdv ee str va vb =
  Array.init (Array.length va) (fun i -> ee va.(i) vb.(i))
  
let elwise_vv ee str vA vB =
  let n = vsize vA in
  if n<>vsize vB then 
    raise (Disaster (Printf.sprintf "elwise size mismatch %s %s %s" (string_of_vector vA) str (string_of_vector vB)));
  match vA, vB with
  | SparseV (_,sva,cva), SparseV (_,svb,cvb) -> let sv, cv = elwise_cvcv ee str sva cva svb cvb in
                                                maybe_dense_v sv n cv

  | SparseV (_,sva,cva), DenseV  dvb         -> let svb,_ = svfreq_v vB in
                                                let sv, cv = elwise_cvcv ee str sva cva svb (sparse_elements_dv svb dvb) in
                                                maybe_dense_v sv n cv
  | DenseV  dva        , SparseV (_,svb,cvb) -> let sva,_ = svfreq_v vA in
                                                let sv, cv = elwise_cvcv ee str sva (sparse_elements_dv sva dva) svb cvb in
                                                maybe_dense_v sv n cv
  | DenseV  dva        , DenseV  dvb         -> maybe_sparse_v (elwise_dvdv ee str dva dvb)

let neg_v = function
  | SparseV (n,sv,cv) -> SparseV (n, cneg sv, List.map (fun (zi,v) -> (zi,cneg v)) cv)
  | DenseV  v         -> DenseV (Array.map cneg v)
  
let track_dotprod = true

(* multiplication of sparse vectors ho hum *)
(* much more complicated now that sv is not always zero *)

let sum_cv n sv cv = let z = cmult_zint sv Z.(n-of_int (List.length cv)) in
                     let cs = List.fold_left (fun cs (_,c) -> c::cs) [z] cv in
                     simplify_csum cs
                  
let dotprod_cvcv n sva cva svb cvb =
  if track_dotprod && (!verbose || !verbose_qcalc) then 
       Printf.printf "dotprod_cvcv %s %s %s %s %s = " (string_of_zint n) (string_of_csnum sva) (string_of_cv cva) 
                                                                         (string_of_csnum svb) (string_of_cv cvb); 
  let sv, cv = elwise_cvcv cprod "*" sva cva svb cvb in
  let r = sum_cv n sv cv in
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

module OrderedZ = struct type t = zint
                         let compare = Z.compare
                         let to_string = string_of_zint
                  end
                      
module ZSet = MySet.Make (OrderedZ)

module CsnumsH = struct type t = csnum list
                      let equal = (=)
                      let hash = Hashtbl.hash
                      let to_string = bracketed_string_of_list string_of_csnum
               end
module CsnumsHash = MyHash.Make (CsnumsH)

(* this is the point of SparseV (and partly SparseM and FuncM): multiplying sparse row by sparse column. *)

(* gives a vector *)
(* I did some experimentation with Grover. Unless sv=c_0 && svv=c_0, there was nothing I could do that made an improvement.
   But there might be some cases nevertheless, so I persist a little
 *)
let raw_mult_cvvcv nr nc sv rf cf svv cv = 
  (* find the rows where the matrix has a non-sparse value that multiplies a non-sparse value in cv *)
  let rset = List.fold_left (fun rset (c,_) -> List.fold_left (fun rset (r,_) -> ZSet.add r rset) 
                                                              rset 
                                                              (cf c)
                            ) 
                            ZSet.empty 
                            cv 
  in
  if sv=c_0 && svv=c_0 then
    (let do_row nxs i = 
       let x = dotprod_cvcv nc sv (rf i) svv cv in
       if x=c_0 then nxs else (i,x)::nxs
     in
     let rs = List.sort Z.compare (ZSet.elements rset) in
     SparseV(nr, c_0, List.rev (List.fold_left do_row [] rs))
    )
  else (* row by row, we have to *)
    (let vec = List.map snd cv in
     let vecv = simplify_csum (List.map (cprod sv) vec) in
     let nv = zlength vec in
     let sv_gap = cprod sv svv in
     let do_other_row (row:csnum list) =
       let rowv = simplify_csum (List.map (cprod svv) row) in
       let gapv = cmult_zint sv_gap (nc-:nv-:zlength row) in
       simplify_csum [rowv; gapv; vecv]
     in
     let dorow_tab = CsnumsHash.create 1000 in
     let do_other_row = CsnumsHash.memofun "dorow_tab" dorow_tab do_other_row in
     let dotprod r = 
       if ZSet.mem r rset then dotprod_cvcv nc sv (rf r) svv cv
                          else do_other_row (List.map snd (rf r))
     in
     try DenseV (Array.init (Z.to_int nr) (dotprod <.> Z.of_int))
     with Z.Overflow -> raise (Disaster (Printf.sprintf "can't make vector size %s in mult_cvvcv" (string_of_zint nr)))
    )

let mult_cvvcv nr nc sv rf cf svv cv = 
  match raw_mult_cvvcv nr nc sv rf cf svv cv with
  | SparseV (n,sv,cv) -> maybe_dense_v sv n cv
  | DenseV  v         -> maybe_sparse_v v
  
let mult_mv m v =
  if !verbose || !verbose_qcalc then 
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
               let _, rf, cf = _The (rowfopt_m m) in
               mult_cvvcv nr nc svm rf cf svv cv
           | FuncM (_,_,_,_,Some (sv,rf,cf)), SparseV (_,svv,cv) -> 
               mult_cvvcv nr nc sv rf cf svv cv
           | DiagM mv, _                                         -> 
               elwise_vv cprod "*" mv v
           | _                                                   -> 
               default ()
  in
  if !verbose || !verbose_qcalc then 
    (Printf.printf "%s\n" (string_of_ket (snum_1, v')); flush_all ());
  v'

let mult_gnv g (n,v) = n, mult_mv (matrix_of_gate g) v

let is_uniform_diag_cvv cvv = 
  match cvv.(0) with
  | [z_0,v] ->  _for_all 1 1 (Array.length cvv) 
                   (fun i -> match cvv.(i) with
                             | [j,x] -> Z.of_int i =: j && x=v
                             | _     -> false
                   )
  | _       -> false
     
  
(* This is not very optimised. But not a priority *)
(* but oh yes it is, because it's used by engate *)
(* it even destroys FuncM. Ho hum. *)
let mult_mm mA mB = 
  if !verbose || !verbose_qcalc then 
    Printf.printf "mult_mm %s %s = " (string_of_matrix mA) (string_of_matrix mB);
  let nrA = rsize mA in
  let ncA = csize mA in
  let nrB = rsize mB in
  if ncA<>nrB then
    raise (Error (Printf.sprintf "matrix size mismatch in multiply: %s * %s"
                                 (string_of_matrix mA)
                                 (string_of_matrix mB)
                 )
          );
  let ncB = csize mB in
  let mC = try match mA, mB with
               | SparseM (ncA,svA,cvvA), SparseM (ncB,svB,cvvB) ->
                 if ncA=ncB && is_uniform_diag_cvv cvvA && is_uniform_diag_cvv cvvB then
                   let get i cvv = try snd (List.hd cvv.(i)) with _ -> raise (Disaster "mult_mm get failure") in
                   let sv' = simplify_csum [cmult_zint (cprod svA svB) (ncA-:z_2); cprod svA (get 0 cvvB); cprod (get 0 cvvA) svB] in
                   let gapv = cmult_zint (cprod svA svB) (ncA-:z_1) in
                   SparseM (ncA, sv', Array.init (Array.length cvvA) 
                                                 (fun i -> [Z.of_int i, csum gapv (cprod (get i cvvA) (get i cvvB))])
                           )
                 else 
                   let (_,rfA, cfA) = _The (rowfopt_m mA) in
                   let (_,rfB, cfB) = _The (rowfopt_m mB) in 
                   (* accumulate the columns of the result *)
                   let colf = raw_mult_cvvcv nrA ncA svA rfA cfA svB <.> cfB <.> Z.of_int in
                   let cvvM' = Array.init (Z.to_int ncB) colf in
                   (* now, because of the way that raw_mult works, we have a matrix which is
                      either all SparseV or all DenseV ...
                    *)
                   let bad () = raise (Can'tHappen (Printf.sprintf "mult_mm cvvM' = %s" 
                                                            (bracketed_string_of_list string_of_vector (Array.to_list cvvM'))
                                                   )
                                      ) 
                   in
                   let m = match cvvM'.(0) with
                           | SparseV (nc,sv',_) -> 
                               let cvv = Array.map (function 
                                                    | SparseV (_,sv,cv) -> cv
                                                    | DenseV _          -> bad ()
                                                   )
                                                   cvvM'
                               in maybe_dense_m sv' ncB (transpose_cvv nc cvv)
                           | DenseV _         ->
                               let m' = Array.map (function 
                                                   | SparseV _ -> bad ()
                                                   | DenseV  v -> v
                                                  )
                                                  cvvM'
                               in maybe_sparse_m m'
                   in
                   transpose_m m
               | DiagM va, DiagM vb                       ->
                   DiagM (elwise_vv cprod "*" va vb)
               | _                                        -> 
                   maybe_sparse_m (init_dm (Z.to_int nrA) (Z.to_int ncB) 
                                          (fun i j -> rowcolprod ncA (?..mA (Z.of_int i)) (revargs ?..mB (Z.of_int j)))
                                  )
             with Z.Overflow -> raise (Disaster (Printf.sprintf "mult_mm (%s,%s) (%s,%s)"
                                                                    (string_of_zint (rsize mA)) (string_of_zint (csize mA))
                                                                    (string_of_zint (rsize mB)) (string_of_zint (csize mB))
                                                )
                                      )
  in
  if !verbose || !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix mC);
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
                                             maybe_sparse_m (init_dm m n (fun i j -> cprod cn (dm.(i).(j))))
           | DiagM (SparseV (n, sv, cv))  -> DiagM (SparseV (n, (cprod cn sv), List.map (fun (i,x) -> i, cprod cn x) cv))
           | DiagM (DenseV dv)            -> DiagM (DenseV (Array.map (cprod cn) dv))
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
           if bm<>snum_1 || km<>snum_1 then 
             raise (Error (Printf.sprintf "bra*ket multiplication with non-unit modulus\n%s\n%s"
                                                 (string_of_ket k) (string_of_bra b)
                          )
                   );
           let default dvA dvB = maybe_sparse_m (Array.map (fun x -> Array.map (cprod x) dvB) dvA) in
           match kv, bv with
           | SparseV (_, svA, cvA), SparseV (_, svB, cvB) ->
                let cvv = transpose_cvv n (Array.make 1 cvA) in
                let sv' = cprod svA svB in
                let rowmult x = sparse_elements_cv (cprod x svB) sv' n (List.map (fun (i,y) -> i, cprod x y) cvB) in
                let svrow = if svA=c_0 then [] else rowmult svA in
                maybe_dense_m sv' n (Array.map (function | [(_,x)] -> rowmult x | _ -> svrow) cvv)
           | SparseV (_, svA, cvA), DenseV  dvB           -> 
                default (densify_cv n svA cvA) dvB
           | DenseV  dvA          , SparseV (_, svB, cvB) -> 
                default dvA (densify_cv n svB cvB)
           | DenseV  dvA          , DenseV  dvB           ->
                default dvA dvB
          )
  in
  if !verbose || !verbose_qcalc then
    (Printf.printf "%s\n" (string_of_matrix r); 
     flush_all();
    );
  r

(* conjugate transpose: transpose and piecewise complex conjugate *)
let cconj_cv = List.map (fun (i,x) -> i, cconj x)

let cconj_v = function DenseV  dv          -> DenseV (Array.map cconj dv)
              |        SparseV (n, sv, cv) -> SparseV (n, cconj sv, cconj_cv cv)

let dagger_m m =
  if rsize m<>csize m then
    raise (Disaster (Printf.sprintf "dagger_m %s" (string_of_matrix m)));
  match m with
  | SparseM (nc, sv, cvv)      -> SparseM (nc, cconj sv, Array.map cconj_cv (transpose_cvv nc cvv))
  | DenseM dm as mA            -> let m = Z.to_int (rsize mA) in
                                  let n = Z.to_int (csize mA) in
                                  DenseM (init_dm m n (fun i j -> cconj (dm.(j).(i))))
  | FuncM (id, rn, cn, f, opt) -> let id = Printf.sprintf "(%s)†" id in
                                  FuncM (id, cn, rn, cconj <..> revargs f, 
                                          opt &~~ (fun (sv, rf, cf) -> Some (cconj sv, cconj_cv <.> cf, cconj_cv <.> rf))
                                        ) 
  | DiagM v                    -> DiagM (cconj_v v)

let dagger_g = dagger_m

let elwise_ff ee str svA rfA svB rfB i = elwise_cvcv ee str svA (rfA i) svB (rfB i)

let rec elwise_mm ee str mA mB =
  if !verbose || !verbose_qcalc then
    (Printf.printf "elwise_mm %s %s %s = " (string_of_matrix mA) str (string_of_matrix mB); 
     flush_all();
    );
  let m = rsize mA in
  let n = csize mA in
  if m<>rsize mB || n<>csize mB then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): elwise_mm %s %s %s"
                                 (string_of_matrix mA)
                                 str
                                 (string_of_matrix mB)
                 )
          );
  let r = match mA, mB with
          | SparseM (_,svA,cvvA)   , SparseM (_,svB,cvvB)    -> 
              let cvv = Array.init (Z.to_int m) (fun i -> snd (elwise_cvcv ee str svA cvvA.(i) svB cvvB.(i))) in
              maybe_dense_m (ee svA svB) n cvv
          | SparseM (nc,svA,cvvA)   , FuncM (_,_,_,_,Some(svB, rf, cf))    -> 
              let cvv = Array.init (Z.to_int m) (fun i -> snd (elwise_cvcv ee str svA cvvA.(i) svB (rf (Z.of_int i)))) in
              maybe_dense_m (ee svA svB) n cvv
          | FuncM (idA,_,_,fA,optA), FuncM (idB,_,_,fB,optB) -> 
              let id = Printf.sprintf "(%s)(%s)" idA idB in
              let opt = match optA, optB with
                        | Some (svA,rfA,cfA), Some (svB,rfB,cfB) -> Some (ee svA svB, (snd <.> elwise_ff ee str svA rfA svB rfB), 
                                                                                      (snd <.> elwise_ff ee str svA cfA svB cfB)
                                                                         )
                        | _                              -> None
              in
              FuncM (id, m, n, (fun i j -> ee (fA i j) (fB i j)), opt)
          | DiagM v1               , DiagM v2                -> DiagM (elwise_vv cprod "*" v1 v2)
          | DiagM v1               , SparseM _               -> elwise_mm ee str (sparse_of_diag v1) mB
          | SparseM _              , DiagM v2                -> elwise_mm ee str mA (sparse_of_diag v2)
          | _                                                -> 
              try maybe_sparse_m (init_dm (Z.to_int m) (Z.to_int n) 
                                          (fun i j -> ee (?..mA (Z.of_int i) (Z.of_int j)) (?..mB (Z.of_int i) (Z.of_int j)))
                                 )
              with Z.Overflow -> raise (Disaster (Printf.sprintf "Overflow in elwise_mm (%s %s %s)" (string_of_zint m) str (string_of_zint n)))
  in
  if !verbose || !verbose_qcalc then
    (Printf.printf "%s\n" (string_of_matrix r); 
     flush_all();
    );
  r

let add_mm = elwise_mm csum "+" 
let sub_mm = elwise_mm cdiff "-"

let neg_m = 
  let cneg_cv = List.map (fun (zi,v) -> (zi,cneg v)) in
  function
  | DenseM  m              -> DenseM (Array.map (Array.map cneg) m)
  | SparseM (n,sv,cvv)     -> SparseM (n, cneg sv, Array.map cneg_cv cvv)
  | DiagM   v              -> DiagM (neg_v v)
  | FuncM   (id,m,n,f,opt) -> let id = Printf.sprintf "-(%s)" id in
                              let opt = match opt with
                                        | Some (sv,rf,cf) -> Some (cneg sv, cneg_cv <.> rf, cneg_cv <.> cf)
                                        | None            -> None
                              in 
                              FuncM (id, m, n, cneg <..> f, opt)
let is_diag_I m = 
  rsize m =: csize m &&
  match m with
  | SparseM (_,sv,cvv) 
      when sv=c_0       -> not (exists_Array (fun i cv -> match cv with 
                                                          | [(j,x)] -> i<>:j || x<>c_1
                                                          | _       -> true
                                             )
                                             cvv
                               )
  | DiagM v             -> (match v with
                            | SparseV (_, sv, []) when sv=c_1 -> true
                            | DenseV  dv                      -> all_Array (fun i x -> x=c_1) dv
                            | _                               -> false
                           )
  | _                   -> not (exists_m (fun i j x -> j=:i && x<>c_1 || j<>:i && x<>c_0) m)

let engate mA =
  if !verbose || !verbose_qcalc then 
    Printf.printf "engate %s " (string_of_matrix mA);
  let m = rsize mA in
  let n = csize mA in
  if m<>:n then raise (Error (Printf.sprintf "non-square engate %s" (string_of_matrix mA)));
  (try ignore (log_2 m) 
   with _ -> raise (Error (Printf.sprintf "matrix size %s is not power of 2 in engate %s" (string_of_zint m) (string_of_matrix mA)))
  );
  let mB = mult_mm mA (dagger_m mA) in
  if not (is_diag_I mB) then
    raise (Error (Printf.sprintf "non-unitary engate %s\n(m*m† = %s)" (string_of_matrix mA) (string_of_matrix mB)));
  let r = gate_of_matrix mA in
  if !verbose || !verbose_qcalc then Printf.printf "OK\n";
  r
  