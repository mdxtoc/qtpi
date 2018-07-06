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
    along with Qtpi; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
    (or look at http://www.gnu.org).
*)

(* this is not (yet) a quantum simulator *)

open Settings
open Array
open Listutils
open Functionutils
open Optionutils

exception Error of string

type qbit = int

type prob = 
  | P_0
  | P_1
  | P_h of int              (* (sqrt 1/2)**n *)
  | P_i                     (* sqrt -1 *)
  | Psymb of bool * qbit    (* false=a, true=b, both random unknowns s.t. a**2+b**2 = 1 *)
  | Pneg of prob
  | Pprod of prob list      (* associative *)
  | Psum of prob list       (* associative *)

type qval = qbit list * prob array (* 2^n probs in the array *)

let string_of_qbit = string_of_int

let short_string_of_qbit = string_of_int

let rec string_of_prob p = 
  (* everything is associative *)
  (* Everything is associative, but the normal form is sum of negated products.
   * So possbra below puts in _very_ visible brackets, for diagnostic purposes.
   *)
  let prio = function
    | P_0
    | P_1
    | P_i             
    | P_h  _ 
    | Psymb _         -> 10
    | Pneg  _         -> 8
    | Pprod _         -> 6
    | Pprod _         -> 8
    | Pneg  _         -> 6
    | Psum  _         -> 4
  in
  let possbra p' = 
    let supprio = prio p in
    let subprio = prio p' in
    let s = string_of_prob p' in
    if subprio<supprio then "(" ^ s ^ ")" else s
    if subprio<=supprio then "!!(" ^ s ^ ")!!" else s
  in
  let nary ps op = String.concat op (List.map possbra ps) in
  match p with
  | P_0             -> "0"
  | P_1             -> "1"
  | P_h 1           -> "h"
  | P_h n           -> Printf.sprintf "h(%d)" n
  | P_i             -> "i"
  | Psymb (b,q)     -> Printf.sprintf "%s%s" (if b then "b" else "a") (string_of_qbit q)
  | Pneg p'         -> "-" ^ possbra p'
  | Pprod ps        -> nary ps "*"
  | Psum  ps        -> nary ps "+"    

and string_of_probvec v =
  let estrings = Array.fold_right (fun p ss -> string_of_prob p::ss) v [] in
  Printf.sprintf "(%s)" (String.concat " <+> " estrings)
  
and string_of_matrix m =
  let strings_of_row r = Array.fold_right (fun p ss -> string_of_prob p::ss) r [] in
  let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
  let rwidth r = List.fold_left max 0 (List.map String.length r) in
  let width = List.fold_left max 0 (List.map rwidth block) in
  let pad s = s ^ String.make (width - String.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}" block
  
and string_of_qval (qs,v) =
  Printf.sprintf "[%s]%s"
                 (string_of_list string_of_qbit ";" qs)
                 (string_of_probvec v)
                
let qstate = Hashtbl.create ?random:(Some true) 100 (* 100? a guess *)

let init () = Hashtbl.reset qstate

let string_of_qstate () = 
  let qqvs = Hashtbl.fold (fun q qv ss -> (Printf.sprintf "%s -> %s"
                                                          (string_of_qbit q)
                                                          (string_of_qval qv)
                                          ) :: ss
                          )
                          qstate
                          []
  in
  Printf.sprintf "{%s}" (String.concat "; " (List.sort compare qqvs))

let qval q = try Hashtbl.find qstate q
             with Not_found -> raise (Error (Printf.sprintf "** Disaster: qval with q=%s qstate=%s"
                                                            (string_of_qbit q)
                                                            (string_of_qstate ())
                                            )
                                     )

let v_0 = Array.init 2 (fun i -> if i=0 then P_1 else P_0)
let v_1 = Array.init 2 (fun i -> if i=0 then P_0 else P_1)
let make_v = Array.of_list

let v_0     = make_v [P_1   ; P_0         ]
let v_1     = make_v [P_0   ; P_1         ]
let v_plus  = make_v [P_h 1 ; P_h 1       ]
let v_minus = make_v [P_h 1 ; Pneg (P_h 1)]

let newqbit = (* hide the reference *)
  (let qbitcount = ref 0 in
   let newqbit () = 
   let newqbit n vopt = 
     let q = !qbitcount in 
     qbitcount := !qbitcount+1; 
     let vec = if !Settings.symbq then
                 Array.init 2 (fun i -> Psymb (i=1, q)) 
               else
                 if Random.bool () then v_0 else v_1
     let vec = match vopt with
               | Some Process.VZero  -> Array.copy v_0
               | Some Process.VOne   -> Array.copy v_1
               | Some Process.VPlus  -> Array.copy v_plus
               | Some Process.VMinus -> Array.copy v_minus
               | None                -> if !Settings.symbq then
                                          Array.init 2 (fun i -> Psymb (i=1, q)) 
                                        else (* random basis, random fixed value *)
                                          Array.copy (if Random.bool () then 
                                                        (if Random.bool () then v_0 else v_1)
                                                      else 
                                                        (if Random.bool () then v_plus else v_minus)
                                                     )
     in
     Hashtbl.add qstate q ([q],vec);
     let qv = [q],vec in
     Hashtbl.add qstate q qv;
     if !verbose_qsim then
       Printf.printf "newqbit %s (%s) -> %s where %s|->%s\n"
                     (Name.string_of_name n)
                     (string_of_option Process.string_of_basisv vopt)
                     (string_of_qbit q)
                     (string_of_qbit q)
                     (string_of_qval qv);
     q
   in
   newqbit
  )

(* The normal form is a sum of possibly-negated products. 
 * Both sums and products are left-recursive.
 * Products are sorted P_0, P_1, P_h, P_i 
 * Products are sorted according to the type definition: i.e.
 * P_0, P_1, P_h, P_i, Psymb.
 *)

  
let rec neg p =
  let r = match p with
          | Pneg p        -> p
          | P_0           -> p
          | Psum ps       -> simplify_sum (List.map neg ps)
          | _             -> Pneg p
  in
  if !verbose_simplify then
    Printf.printf "neg (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r
    
and prod p1 p2 =
  let r = match p1, p2 with
          | Pneg p1         , _                 -> neg (prod p1 p2)
          | _               , Pneg p2           -> neg (prod p1 p2)
          | _               , Psum p2s          -> simplify_sum (List.map (prod p1) p2s)
          | Psum p1s        , _                 -> simplify_sum (List.map (fun p1 -> prod p1 p2) p1s)
          | Pprod p1s       , Pprod p2s         -> simplify_prod (p1s @ p2s)
          | _               , Pprod p2s         -> simplify_prod (p1 :: p2s)
          | Pprod p1s       , _                 -> simplify_prod (p1s @ [p2])
          | _                                   -> simplify_prod [p1;p2]
  in
  if !verbose_simplify then
    Printf.printf "prod (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and simplify_prod ps = (* basically we deal with constants *)
  let r = let rec sp is_neg r ps = 
            match ps with
            | P_0            :: ps -> false, [P_0]
            | P_1            :: ps -> sp is_neg r ps
            | P_i   :: P_i   :: ps -> sp (not is_neg) r ps
            | P_h i :: P_h j :: ps -> sp is_neg r (sqrt_half (i+j) :: ps)
            | p              :: ps -> sp is_neg (p::r) ps
            | []                   -> is_neg, List.rev r
          in
          let is_neg, ps = sp false [] (List.sort compare ps) in
          let p = match ps with 
                  | []  -> P_1
                  | [p] -> p 
                  | _   -> Pprod ps 
          in
          if is_neg then neg p else p
  in
  if !verbose_simplify then
    Printf.printf "simplify_prod (%s) -> %s\n" (string_of_prob (Pprod ps)) (string_of_prob r);
  r

and sum  p1 p2 = 
  let r = match p1, p2 with
          | Psum p1s, Psum p2s  -> simplify_sum (p1s @ p2s)
          | _       , Psum p2s  -> simplify_sum (p1 :: p2s)
          | Psum p1s, _         -> simplify_sum (p1s @ [p2]) 
          | _                   -> simplify_sum [p1;p2]
  in
  if !verbose_simplify then
    Printf.printf "sum (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and simplify_sum ps = 
  let r = let rec scompare p1 p2 =
            match p1, p2 with
            | Pneg p1  , _         -> let r = scompare p1 p2 in if r=0 then 1 else 0
            | _        , Pneg p2   -> scompare p1 p2
            | Pprod p1s, Pprod p2s -> Pervasives.compare p1s p2s
            | _                    -> Pervasives.compare p1 p2
          in
          let rec double p1 p2 = (* looking for h(k)*X+h(k)*X. We know p1=p2 *)
            match p1, p2 with
            | Pneg p1           , Pneg p2                          
                    -> double p1 p2 &~~ (_Some <.> neg)
            | Pprod (P_h i::p1s), Pprod (P_h j::p2s) when i>=2                               
                    -> Some (simplify_prod (sqrt_half (i-2) :: p1s))
            | _     -> None
            let r = match p1, p2 with
                    | Pneg p1           , Pneg p2                          
                            -> double p1 p2 &~~ (_Some <.> neg)
                    | Pprod (P_h i::p1s), Pprod (P_h j::p2s) when i>=2                               
                            -> Some (simplify_prod (sqrt_half (i-2) :: p1s))
                    | P_h i             , P_h j              when i>=2                               
                            -> Some (sqrt_half (i-2))
                    | _     -> None
            in
            if !verbose_simplify then
              Printf.printf "double (%s) (%s) -> %s\n" (string_of_prob p1)  
                                                       (string_of_prob p2)
                                                       (string_of_option string_of_prob r);
            r
          in
          let rec a2b2 p1 p2 = (* looking for X*a**2+X*b**2 *)
            match p1, p2 with
            | Pneg p1  , Pneg p2   -> a2b2 p1 p2 &~~ (_Some <.> neg)
            | Pprod p1s, Pprod p2s ->
                (try let pps = zip p1s p2s in
                     let rec partition_1 r pps =
                       match pps with
                       | (a,b) as h :: pps when a=b -> partition_1 (h::r) pps
                       | _                          -> List.rev r, pps
                     in
                     let pre, rest = partition_1 [] pps in
                     let all_same pps =
                       let pre, post = partition_1 [] pps in
                       null post
                     in
                     match rest with
                     | (Psymb (false, q1), Psymb (true, q2)) ::
                       (Psymb (false, q3), Psymb (true, q4)) :: post  
                       when q1=q2 && q1=q3 && q1=q4 && all_same post
                             -> let pre, _ = unzip pre in
                                let post, _ = unzip post in
                                Some (simplify_prod (pre @ post))
                     | _     -> None
                 with Zip -> None
                )
            | _ -> None
            let r = match p1, p2 with
                    | Pneg p1  , Pneg p2   -> a2b2 p1 p2 &~~ (_Some <.> neg)
                    | Pprod p1s, Pprod p2s ->
                        (try let pps = zip p1s p2s in
                             let rec partition_1 r pps =
                               match pps with
                               | (a,b) as h :: pps when a=b -> partition_1 (h::r) pps
                               | _                          -> List.rev r, pps
                             in
                             let pre, rest = partition_1 [] pps in
                             let all_same pps =
                               let pre, post = partition_1 [] pps in
                               null post
                             in
                             match rest with
                             | (Psymb (false, q1), Psymb (true, q2)) ::
                               (Psymb (false, q3), Psymb (true, q4)) :: post  
                               when q1=q2 && q1=q3 && q1=q4 && all_same post
                                     -> let pre , _ = unzip pre in
                                        let post, _ = unzip post in
                                        Some (simplify_prod (pre @ post))
                             | _     -> None
                         with Zip -> None
                        )
                    | _ -> None
            in
            if !verbose_simplify then
              Printf.printf "a2b2 (%s) (%s) -> %s\n" (string_of_prob p1)  
                                                     (string_of_prob p2)
                                                     (string_of_option string_of_prob r);
            r
          in
          let rec sp again r ps =
            match ps with
            | P_0                :: ps            -> sp again r ps
            | Pneg p1 :: p2      :: ps when p1=p2 -> sp again r ps
            | p1      :: Pneg p2 :: ps when p1=p2 -> sp again r ps
            | p1      :: p2      :: ps when p1=p2 -> (match double p1 p2 with
                                                      | Some p -> sp true (p::r) ps
                                                      | None   -> sp again (p1::r) (p2::ps)
                                                     )
            | p1      :: p2      :: ps            -> (match a2b2 p1 p2 with
                                                      | Some p -> sp true (p::r) ps
                                                      | None   -> sp again (p1::r) (p2::ps)
                                                     )
            | p                  :: ps            -> sp again (p::r) ps
            | []                                  -> let r = List.rev r in
                                                     if again then doit r else r
                                                    if again then doit r else r
          and doit ps = sp false [] (List.sort scompare ps)
          in
          match doit ps with
          | []  -> P_0
          | [p] -> p
          | ps  -> Psum ps
  in
  if !verbose_simplify then
    Printf.printf "simplify_sum (%s) -> %s\n" (string_of_prob (Psum ps)) (string_of_prob r);
  r


and sqrt_half i =   (* (1/sqrt 2)**i *)
  let r = if i=0 then P_1 else P_h i in
  if !verbose_simplify then
    Printf.printf "sqrt_half %d -> %s\n" i (string_of_prob r);
  r

and r2 p = (* multiply by sqrt 2 (=1/h). Happens: see normalise *)
  let r = match p with
          | P_0                 -> p
          | P_h i when i>=1     -> sqrt_half (i-1)
          | Pneg p              -> neg (r2 p)
          | Pprod ps            -> simplify_prod (List.map r2 ps)
          | Psum  ps            -> simplify_sum  (List.map r2 ps)
          | _                   -> raise (Error (Printf.sprintf "r2 %s" (string_of_prob p)))
          | P_0                             -> p
          | Pneg p                          -> neg (r2 p)
          | Pprod (P_h i::ps)   when i>=1   -> simplify_prod (sqrt_half (i-1) :: ps)
          | P_h i               when i>=1   -> sqrt_half (i-1)
          | Psum  ps                        -> simplify_sum  (List.map r2 ps)
          | _                               -> raise (Error (Printf.sprintf "r2 %s" (string_of_prob p)))
  in
  if !verbose_simplify then
    Printf.printf "r2 (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r

and div p1 p2 = (* happens in normalise *) (* this needs work for division by sums and also for division by products *)
  let bad () = 
    raise (Error (Printf.sprintf "div (%s) (%s)" (string_of_prob p1) (string_of_prob p2)))
  in
  let r = match p1 with
          | P_0               -> P_0
          | _ when p1=p2      -> P_1
          | Pprod ps          -> let rec del ps =
                                   match ps with
                                   | [] -> bad()
                                   | p::ps -> if p=p2 then ps else p::del ps
                                 in
                                 Pprod (del ps)
          | Psum ps           -> simplify_sum (List.map (fun p -> div p p2) ps)
          | _                 -> bad ()
  in
  if !verbose_simplify then
    Printf.printf "div (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r
  
let make_ug rows = rows |> (List.map Array.of_list) |> (Array.of_list)

let mH  = make_ug [[P_h 1  ; P_h 1      ];
                   [P_h 1  ; neg (P_h 1)]]
let mI  = make_ug [[P_1    ; P_0        ];
                   [P_0    ; P_1        ]] 
let mX  = make_ug [[P_0    ; P_1        ];
                   [P_1    ; P_0        ]] 
let mY  = make_ug [[P_0    ; P_1        ];
                   [neg P_1; P_0        ]] 
let mYi = make_ug [[P_0    ; neg P_i    ];
                   [P_i    ; P_0        ]] 
let mZ =  make_ug [[P_1    ; P_0        ];
                   [P_0    ; neg P_1    ]] 

let mPhi = function
  | 0 -> mI
  | 1 -> mX
  | 2 -> mYi
  | 3 -> mZ
  | i -> raise (Error ("** Disaster: _Phi(" ^ string_of_int i ^ ")"))

let mCnot = make_ug [[P_1; P_0; P_0; P_0];
                     [P_0; P_1; P_0; P_0];
                     [P_0; P_0; P_0; P_1];
                     [P_0; P_0; P_1; P_0]]
                     
let m_1 = make_ug [[P_1]] (* a unit for folding *)
let m_0 = make_ug [[P_0]] (* another unit for folding *)

(* from here on down, I just assume (hope) that we are working with square matrices *)
(* maybe later that typechecking trick ... *)

let new_v n = Array.make n P_0
let new_ug n = Array.make_matrix n n P_0

let vsize = Array.length
let msize = Array.length

let _for i inc n f = (* n is size, so up to n-1 *)
  let rec rf i =
    if i<n then (f i; rf (i+inc)) (* else skip *)
  in
  rf i
  
let _forlf i inc n f v =
let _for_leftfold i inc n f v =
  let rec ff i v =
    if i<n then ff (i+inc) (f i v) else v
  in
  ff i v

let rec _forrf i inc n f v =
let rec _for_righttfold i inc n f v =
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
  
let bigI n = let m = Array.make_matrix n n P_0 in
             _for 0 1 n (fun i -> m.(i).(i) <- P_1);
             m
             
let tensor_v vA vB =
  let nA = vsize vA in
  let nB = vsize vB in
  let vR = new_v (nA*nB) in
  _for 0 1 nA (fun i -> _for 0 1 nB (fun j -> vR.(i*nB+j) <- prod vA.(i) vB.(j)));
  if !verbose_qsim then Printf.printf "%s (><) %s -> %s\n"
                                     (string_of_probvec vA)
                                     (string_of_probvec vB)
                                     (string_of_probvec vR);
  if !verbose_qcalc then Printf.printf "%s (><) %s -> %s\n"
                                       (string_of_probvec vA)
                                       (string_of_probvec vB)
                                       (string_of_probvec vR);
  vR
  
let tensor_m mA mB =
  let nA = msize mA in
  let nB = msize mB in
  let mt = new_ug (nA*nB) in
  _for 0 1 nA (fun i -> 
                 _for 0 1 nA (fun j -> 
                                let aij = mA.(i).(j) in
                                _for 0 1 nB (fun m ->
                                               _for 0 1 nB (fun p ->
                                                              mt.(i*nB+p).(j*nB+m) <- prod aij (mB.(m).(p))
                                                           )
                                            )
                             )
              );
   mt

let do_mv m v =
  let n = Array.length v in
  if msize m <> n then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): do_mv %s %s"
                                 (string_of_matrix m)
                                 (string_of_probvec v)
                 )
          );
  let v' = new_v n in
  _for 0 1 n (fun i -> 
                v'.(i) <- _forrf 0 1 n (fun j -> sum (prod m.(i).(j) v.(j))) P_0
                v'.(i) <- _for_righttfold 0 1 n (fun j -> sum (prod m.(i).(j) v.(j))) P_0
             );
  v'
  
let mIH = tensor_m mI mH
let mHI = tensor_m mH mI

type ugv =
  | GateH
  | GateI
  | GateX
  | GateCnot
  | GatePhi of int

let string_of_ugv = function
  | GateH           -> "_H"
  | GateI           -> "_I"
  | GateX           -> "_X"
  | GateCnot        -> "_Cnot"
  | GatePhi (i)     -> "_Phi(" ^ string_of_int i ^ ")"

let matrix_of_ugv = function
  | GateH           -> mH
  | GateI           -> mI
  | GateX           -> mX
  | GateCnot        -> mCnot
  | GatePhi (i)     -> mPhi(i)

  
let idx q qs = 
  let fail () = raise (Error (Printf.sprintf "** Disaster: %s not in (%s)" 
                                             (string_of_qbit q) 
                                             (string_of_list string_of_qbit "," qs)
                 
                             )
                      )
  in 
  let rec f i = function
    | q'::qs -> if q = q' then i else f (i+1) qs
    | []     -> fail()
  in
  f 0 qs

let ibit q qs =
  let i = idx q qs in
  1 lsl (List.length qs-i-1)

let try_split v =
  let id_string () = Printf.sprintf "try_split %s" (string_of_probvec v) in
  if !verbose_qcalc then 
    print_string (id_string ());
  let n = vsize v in
  let nh = vsize v / 2 in
  let r = (* if the first half is all zeros then use v_1, which is 0+1 *)
          if _for_all 0 1 nh (fun i -> v.(i)=P_0) then
            Some (Array.copy v_1, Array.init nh (fun i -> v.(nh+i)))
          else
          (* if the second half is all zeros then use v_0, which is 1+0 *)
          if _for_all nh 1 n (fun i -> v.(i)=P_0) then
            Some (Array.copy v_0, Array.init nh (fun i -> v.(i)))
          else
            None
  in
  if !verbose_qcalc then
    Printf.printf " -> %s\n" 
                  (string_of_option (fun (v,v') -> Printf.sprintf "%s, %s" 
                                                   (string_of_probvec v) 
                                                   (string_of_probvec v')
                                    )
                                    r
                  );
  r
  
let rec record ((qs, vq) as qv) =
   let doit q = if !verbose_qsim then
                  Printf.printf "recording %s|->%s\n" (string_of_qbit q) (string_of_qval qv);
                Hashtbl.replace qstate q qv 
   in
   match qs with
   | []     -> raise (Error (Printf.sprintf "record gets %s" (string_of_qval qv)))
   | [q]    -> doit q
   | q::qs'  -> (* try to split it up *)
               match try_split vq with
               | Some (vq,v') -> record ([q], vq); record (qs', v')
               | None         -> List.iter doit qs

let ugstep qs ugv = 
  let id_string () = Printf.sprintf (if List.length qs =1 then "ugstep %s >> %s" else "ugstep [%s] >> %s")
                                    (string_of_list string_of_qbit ";" qs)
                                    (string_of_ugv ugv)
  in
  (* let noway s = Printf.printf "can't yet handle %s %s\n" (id_string ()) s in *)

  let doit_1 q m =
    match qval q with
    | qs, v -> let nqs = List.length qs in
               let i = idx q qs in
               let m_op =
                 if i=0 && nqs=1 then m 
                 else (let pre_m = _forlf 0 1 i (fun _ mIs -> tensor_m mI mIs) m_1 in
                       let post_m = _forlf (i+1) 1 nqs (fun _ mIs -> tensor_m mI mIs) m_1 in
                 else (let pre_m = _for_leftfold 0 1 i (fun _ mIs -> tensor_m mI mIs) m_1 in
                       let post_m = _for_leftfold (i+1) 1 nqs (fun _ mIs -> tensor_m mI mIs) m_1 in
                       let m_op = tensor_m (tensor_m pre_m m) post_m in
                       if !verbose_qsim then
                       if !verbose_qcalc then
                         Printf.printf "pre_m = %s, m= %s, post_m = %s, m_op = %s\n" 
                                       (string_of_matrix pre_m)
                                       (string_of_matrix m)
                                       (string_of_matrix post_m)
                                       (string_of_matrix m_op);
                        m_op
                       )
               in
               let v' = do_mv m_op v in
               if !verbose_qsim then 
                 Printf.printf "%s : %s -> %s\n"
                 Printf.printf "%s : was %s|->%s; now %s->%s\n"
                               (id_string ())
                               (string_of_qbit q)
                               (string_of_qval (qs, v))
                               (string_of_qbit q)
                               (string_of_qval (qs, v'));
               let qv = qs,v' in
               List.iter (fun q -> Hashtbl.replace qstate q qv) qs;
               record (qs,v')
    
  in
  
  let doit_Cnot q1 q2 =
    if q1=q2 then raise (Error (Printf.sprintf "** Disaster (same qbit twice in Cnot) %s" (id_string ())));
    match qval q1, qval q2 with
    | (q1s, v1), (q2s, v2) -> (* these lists _have_ to be different. I'm not going to check. *)
        let v = tensor_v v1 v2 in
        let qs = q1s @ q2s in
        let bit1 = ibit q1 qs in
        let bit2 = ibit q2 qs in
        let mCnot = bigI (vsize v) in
        if !verbose_qsim then
        if !verbose_qcalc then
          Printf.printf "bit1=%d, bit2=%d\n" bit1 bit2;
        Array.iteri (fun i r -> if (i land bit1)<>0 && (i land bit2)=0 then 
                                    (let i' = i lor bit2 in
                                     if !verbose_qsim then 
                                     if !verbose_qcalc then 
                                       Printf.printf "swapping rows %d and %d\n" i i';
                                     let temp = mCnot.(i) in
                                     mCnot.(i) <- mCnot.(i');
                                     mCnot.(i') <- temp
                                    )
                     ) mCnot;
        if !verbose_qsim then
        if !verbose_qcalc then
          Printf.printf "mCnot = %s\n" (string_of_matrix mCnot);
        let v' = do_mv mCnot v in
        let qv = qs, v' in
        if !verbose_qsim then 
          Printf.printf "%s : %s, %s -> %s\n"
          Printf.printf "%s : %s|->%s; %s|->%s; now %s,%s|->%s\n"
                        (id_string ())
                        (string_of_qbit q1)
                        (string_of_qval (qval q1))
                        (string_of_qbit q2)
                        (string_of_qval (qval q2))
                        (string_of_qbit q1)
                        (string_of_qbit q2)
                        (string_of_qval qv);
        List.iter (fun q -> Hashtbl.replace qstate q qv) qs;
  in
  match qs, ugv with
  | [q]    , GateH       
  | [q]    , GateI      
  | [q]    , GateX      
  | [q]    , GatePhi _  -> doit_1 q (matrix_of_ugv ugv)
  | [q1;q2], GateCnot   -> doit_Cnot q1 q2 
  | _                   -> raise (Error (Printf.sprintf "** Disaster: ugstep [%s] %s"
                                                        (string_of_list string_of_qbit ";" qs)
                                                        (string_of_ugv ugv)
                                        )
                                 )

let qmeasure q = 
  let qs, v = qval q in
  let bit = ibit q qs in
  let prob = 
    _forlf 0 1 (vsize v) (fun i p -> if i land bit<>0 then 
    _for_leftfold 0 1 (vsize v) (fun i p -> if i land bit<>0 then 
                                      sum (prod v.(i) v.(i)) p 
                                    else p
                        ) 
                        P_0 
  in
  if !verbose_qsim then 
    Printf.printf "qmeasure %s (%s) -> %s"
                  (string_of_qbit q)
                  (string_of_qval (qval q))
                  (string_of_prob prob);
  let guess () =
    let r = if Random.bool () then 0 else 1 in
    if !verbose_qsim then print_endline (" (guessing " ^ string_of_int r ^ ")");
    r  
  in
  let r = match prob with
  | P_0    -> 0
  | P_1    -> 1
  | P_h i -> if i=0 then 1
              else (let rg = Random.float 1.0 in
                    let rec iexp i rf = if i=0 then rf else iexp (i-1) (rf/.2.0) in
                    if iexp i 1.0 < rg then 1 else 0
                   )
  | _     -> guess ()
  in
  (* set the relevant probs to zero, normalise *)
  _for 0 1 (vsize v) (fun i -> if (r=1 && i land bit=0) || (r=0 && i land bit<>0)
                               then v.(i) <- P_0 (* else skip *)
                     );
  let modulus = _forlf 0 1 (vsize v) (fun i p -> sum (prod v.(i) v.(i)) p) P_0 in
  if !verbose_qsim then Printf.printf " (un-normalised %s modulus %s)" (string_of_qval (qs,v)) (string_of_prob modulus);
  let modulus = _for_leftfold 0 1 (vsize v) (fun i p -> sum (prod v.(i) v.(i)) p) P_0 in
  if !verbose_qcalc then 
    Printf.printf " (un-normalised %s modulus %s);" (string_of_qval (qs,v)) (string_of_prob modulus);
  (match modulus with
   | P_1                -> ()
   | P_h k  when k mod 2 = 0 
                        -> let n = k/2 in
                           (* multiply by 2**(n/2) *)
                           let halfn = n/2 in
                           _for 0 1 halfn (fun _ -> _for 0 1 (vsize v) (fun i -> v.(i) <- sum v.(i) v.(i)));
                           if n mod 2 = 1 then
                             _for 0 1 (vsize v) (fun i -> v.(i) <- r2 v.(i))
   | Pprod [p1;p2] when p1=p2 
                        -> _for 0 1 (vsize v) (fun i -> v.(i) <- div v.(i) p1)
   | _                  -> if !verbose_qsim then 
                             Printf.printf " oh dear!\n"; 
                           raise (Error (Printf.sprintf "normalise %s modulus %s" 
                                                        (string_of_qval (qs,v)) 
                                                        (string_of_prob modulus)
                                        )
                                 )
  );
  if !verbose_qsim then 
    Printf.printf " (normalised %s) = %d\n" (string_of_qval (qs,v)) r;
  r