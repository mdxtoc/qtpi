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
open Array
open Listutils
open Functionutils
open Optionutils
open Tupleutils

exception Error of string

type qbit = int
(* h = sqrt (1/2) = cos (pi/4) = sin (pi/4); useful for rotation pi/4, or 45 degrees;
   f = sqrt ((1+h)/2) = cos (pi/8); useful for rotation pi/8 or 22.5 degrees;
   g = sqrt ((1-h)/2) = sin (pi/8); the partner of h;
   i = sqrt -1; will be useful if we ever go complex.
   
   Note h^2=1/2; 
        f^2+g^2=1;
        f^2-g^2=h;
        fg = 1/2h  
 *)
type prob = 
  | P_0
  | P_1
  | P_f of int              
  | P_g of int
  | P_h of int              
  | P_i                     
  | Psymb of bool * qbit    (* false=a, true=b, both random unknowns s.t. a**2+b**2 = 1 *)
  | Pneg of prob
  | Pprod of prob list      (* associative *)
  | Psum of prob list       (* associative *)

type qval = qbit list * prob array (* with n qbits, 2^n probs in the array *)

let string_of_qbit = string_of_int

let short_string_of_qbit = string_of_int

let rec string_of_prob p = 
  (* Everything is associative, but the normal form is sum of negated products.
   * So possbra below puts in _very_ visible brackets, for diagnostic purposes.
   *)
  let prio = function
    | P_0
    | P_1
    | P_i             
    | P_f  _ 
    | P_g  _ 
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
  let nary ps op = String.concat op (List.map possbra ps) in
  match p with
  | P_0             -> "0"
  | P_1             -> "1"
  | P_f 1           -> "f"
  | P_f n           -> Printf.sprintf "f(%d)" n
  | P_g 1           -> "g"
  | P_g n           -> Printf.sprintf "g(%d)" n
  | P_h 1           -> "h"
  | P_h n           -> Printf.sprintf "h(%d)" n
  | P_i             -> "i"
  | Psymb (b,q)     -> Printf.sprintf "%s%s" (if b then "b" else "a") (string_of_qbit q)
  | Pneg p'         -> "-" ^ possbra p'
  | Pprod ps        -> nary ps "*"
  | Psum  ps        -> nary ps "+"    

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
  
let rec string_of_probvec v =
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
     let sign s ss = match Stringutils.first s, ss with
                     | _  , [] 
                     | '-', _   -> s::ss
                     | _        -> ("+" ^ s)::ss 
     in
     let string_of_amplitude p = 
       match p with
       | P_0                (* can't happen *)
       | P_1                (* can't happen *)
       | P_i             
       | P_f  _ 
       | P_g  _ 
       | P_h  _ 
       | Psymb _         
       | Pprod _         -> string_of_prob p
       | Pneg  p'        -> (match p' with
                                   | P_0       -> "(-0? really?)"
                                   | P_1       -> "-"
                                   | P_i             
                                   | P_h   _ 
                                   | Psymb _   -> "-" ^ string_of_prob p'
                                   | _         -> "-(" ^ string_of_prob p' ^ ")"
                                  )
       | Psum  _         -> "(" ^ string_of_prob p ^ ")"
     in
     let string_of_basis_idx i =
       Printf.sprintf "|%s>" (string_of_bin i)
     in
     let estrings = _for_leftfold 0 1 n
                        (fun i ss -> match v.(i) with
                                     | P_0 -> ss
                                     | P_1 -> sign (string_of_basis_idx i) ss
                                     | _   -> sign (Printf.sprintf "%s%s" 
                                                                    (string_of_amplitude v.(i)) 
                                                                    (string_of_basis_idx i)
                                                    )
                                                    ss
                        )
                        []
     in
     match estrings with
     | []  -> "??empty probvec??"
     | [e] -> e
     | _   -> Printf.sprintf "(%s)" (String.concat "" (List.rev estrings))
    )
  else
    (let estrings = Array.fold_right (fun p ss -> string_of_prob p::ss) v [] in
     Printf.sprintf "(%s)" (String.concat " <+> " estrings)
    )
  
and string_of_matrix m =
  let strings_of_row r = Array.fold_right (fun p ss -> string_of_prob p::ss) r [] in
  let block = Array.fold_right (fun r ss -> strings_of_row r::ss) m [] in
  let rwidth r = List.fold_left max 0 (List.map String.length r) in
  let width = List.fold_left max 0 (List.map rwidth block) in
  let pad s = s ^ String.make (width - String.length s) ' ' in
  let block = String.concat "\n "(List.map (String.concat " " <.> List.map pad) block) in
  Printf.sprintf "\n{%s}" block
  
and string_of_qval (qs,v) =
  match qs with
  | [_] -> string_of_probvec v
  | _   -> Printf.sprintf "[%s]%s"
                          (string_of_list string_of_qbit ";" qs)
                          (string_of_probvec v)
                
let qstate = Hashtbl.create ?random:(Some true) 100 (* 100? a guess *)

let init () = Hashtbl.reset qstate

let string_of_qstate () = 
  let qqvs = Hashtbl.fold (fun q qv ss -> (q,qv) :: ss) qstate []
  in
  Printf.sprintf "{%s}" (string_of_list (string_of_pair string_of_qbit string_of_qval " -> ") "; " (List.sort Pervasives.compare qqvs))

let qval q = try Hashtbl.find qstate q
             with Not_found -> raise (Error (Printf.sprintf "** Disaster: qval with q=%s qstate=%s"
                                                            (string_of_qbit q)
                                                            (string_of_qstate ())
                                            )
                                     )

let make_v = Array.of_list

let v_0     = make_v [P_1   ; P_0         ]
let v_1     = make_v [P_0   ; P_1         ]
let v_plus  = make_v [P_h 1 ; P_h 1       ]
let v_minus = make_v [P_h 1 ; Pneg (P_h 1)]

(* ****************** new and dispose for qbits ******************************* *)

let newqbit, disposeqbit, string_of_qfrees, string_of_qlimbo = (* hide the references *)
  let qbitcount = ref 0 in
  let qfrees = ref [] in
  let qlimbo = ref [] in
  let newqbit pn n vopt = 
    let q = match !qfrees, vopt with
      | q::qs, Some _ -> qfrees:=qs; q (* only re-use qbits when we don't make symbolic probabilities *)
                                       (* note this is a space leak, but a small one *)
      | _             -> let q = !qbitcount in 
                         qbitcount := q+1; 
                         q
    in
    let vec = match vopt with
              | Some Basisv.BVzero  -> Array.copy v_0
              | Some Basisv.BVone   -> Array.copy v_1
              | Some Basisv.BVplus  -> Array.copy v_plus
              | Some Basisv.BVminus -> Array.copy v_minus
              | None                -> if !Settings.symbq then
                                         Array.init 2 (fun i -> Psymb (i=1, q)) (* this could be a bug if we used qfrees *)
                                       else (* random basis, random fixed value *)
                                         Array.copy (match Random.bool (), Random.bool ()  with
                                                     | false, false -> v_0 
                                                     | false, true  -> v_1
                                                     | true , false -> v_plus 
                                                     | true , true  -> v_minus
                                                    )
    in
    let qv = [q],vec in
    Hashtbl.add qstate q qv;
    if !verbose || !verbose_qsim then
      Printf.printf "%s newqbit %s (%s) -> %s; now %s|->%s\n"
                    (Name.string_of_name pn)
                    (Name.string_of_name n)
                    (string_of_option Basisv.string_of_basisv vopt)
                    (string_of_qbit q)
                    (string_of_qbit q)
                    (string_of_qval qv);
    q
  in
  let disposeqbit pn q = 
    if !verbose || !verbose_qsim then
      Printf.printf "%s disposes %s " (Name.string_of_name pn) (string_of_qbit q);
    match Hashtbl.find qstate q with
                      | [q],_ -> Hashtbl.remove qstate q; qfrees := q::!qfrees;
                                 if !verbose || !verbose_qsim then
                                   Printf.printf "to qfrees %s\n" (bracketed_string_of_list string_of_qbit !qfrees)
                      | qv    -> (* don't dispose entangled qbits *)
                                 if !verbose || !verbose_qsim then
                                   Printf.printf "to qlimbo %s\n" (bracketed_string_of_list 
                                                                     (fun q -> Printf.sprintf "%s|->%s"
                                                                                              (string_of_qbit q)
                                                                                              (string_of_qval (Hashtbl.find qstate q))
                                                                     )
                                                                     !qlimbo
                                                                  )
                                                 ;
                                 qlimbo := q::!qlimbo
  in
  let string_of_qfrees () = bracketed_string_of_list string_of_qbit !qfrees in
  let string_of_qlimbo () = bracketed_string_of_list string_of_qbit !qlimbo in
  newqbit, disposeqbit, string_of_qfrees, string_of_qlimbo
  
let strings_of_qsystem () = [Printf.sprintf "qstate=%s" (string_of_qstate ());
                             Printf.sprintf "qfrees=%s" (string_of_qfrees ());
                             Printf.sprintf "qlimbo=%s" (string_of_qlimbo ())
                            ]

(* *********************** simplification starts here ************************************ *)

(* The normal form is a sum of possibly-negated products. 
 * Both sums and products are left-recursive.
 * Products are sorted according to the type definition: i.e.
 * P_0, P_1, P_f, P_g, P_h, P_i, Psymb. But ... this isn't good enough. 
 
 * We need to sort identifiers according to their suffix: a0,b0,a1,b1, ...
 *)

let probcompare p1 p2 =
  match p1, p2 with
  | Psymb (b1,q1), Psymb (b2,q2) -> Pervasives.compare (q1,b1) (q2,b2)
  | _                            -> Pervasives.compare p1      p2

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
          | _               , Psum p2s          -> let ps = List.map (prod p1) p2s in
                                                   simplify_sum (sflatten ps)
          | Psum p1s        , _                 -> let ps = List.map (fun p1 -> prod p1 p2) p1s in
                                                   simplify_sum (sflatten ps)
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
          let is_neg, ps = sp false [] (List.sort probcompare ps) in
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
and sum p1 p2 = 
  let r = match p1, p2 with
          | Psum p1s, Psum p2s  -> simplify_sum (p1s @ p2s)
          | _       , Psum p2s  -> simplify_sum (p1 :: p2s)
          | Psum p1s, _         -> simplify_sum (p1s @ [p2]) 
          | _                   -> simplify_sum [p1;p2]
  in
  if !verbose_simplify then
    Printf.printf "sum (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and sflatten ps = (* flatten a list of sums *)
  let rec sf p ps = 
    match p with
    | Psum ps' -> ps' @ ps
    | _        -> p :: ps
  in
  let r = List.fold_right sf ps [] in
  if !verbose_simplify then
    Printf.printf "sflatten %s -> %s\n" 
                  (bracketed_string_of_list string_of_prob ps) 
                  (bracketed_string_of_list string_of_prob r);
  r

and simplify_sum ps = 
  let r = let rec scompare p1 p2 = (* ignore negation *)
            match p1, p2 with
            | Pneg p1  , _         -> scompare p1 p2
            | _        , Pneg p2   -> scompare p1 p2
            (* | Pprod p1s, Pprod p2s -> probcompare p1s p2s *)
            | _                    -> probcompare p1 p2
          in
          let rec double p1 = (* looking for h(k)*X+h(k)*X. We know p1=p2 *)
            let r = match p1 with
                    | Pneg p1                        
                            -> double p1 &~~ (_Some <.> neg)
                    | Pprod (P_h i::p1s) when i>=2                               
                            -> Some (simplify_prod (sqrt_half (i-2) :: p1s))
                    | P_h i              when i>=2                               
                            -> Some (sqrt_half (i-2))
                    | _     -> None
            in
            if !verbose_simplify then
              Printf.printf "double (%s) -> %s\n" (string_of_prob p1)  
                                                  (string_of_option string_of_prob r);
            r
          in
          let rec a2b2 p1 p2 = (* looking for X*a^2+X*b^2; also X*f^2+X*g^2. *)
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
                             | (P_f i, P_g j) :: post
                               when i=j && i mod 2 = 0 && all_same post
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
            | p1      :: p2      :: ps when p1=p2 -> (match double p1 with
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
          and doit ps = sp false [] (List.sort scompare ps)
          in
          if List.exists (function Psum _ -> true | Pneg (Psum _) -> true | _ -> false) ps then
            raise (Error (Printf.sprintf "simplify_sum (%s)" (string_of_prob (Psum ps))))
          else
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
          | Pneg p1           -> neg (div p1 p2)
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

let m_I  = make_ug  [[P_1       ; P_0        ];
                     [P_0       ; P_1        ]] 
let m_X  = make_ug  [[P_0       ; P_1        ];
                     [P_1       ; P_0        ]] 
let m_Y  = make_ug  [[P_0       ; P_1        ];
                     [neg P_1   ; P_0        ]] 
let mYi = make_ug   [[P_0       ; neg P_i    ];
                     [P_i       ; P_0        ]] 
let m_Z =  make_ug  [[P_1       ; P_0        ];
                     [P_0       ; neg P_1    ]] 

let m_H  = make_ug [[P_h 1      ; P_h 1      ];
                    [P_h 1      ; neg (P_h 1)]]

let m_FG = make_ug [[P_f 1      ; P_g 1      ];
                    [neg (P_g 1); P_f 1      ]]

let m_Phi = function
  | 0 -> m_I
  | 1 -> m_X
  | 2 -> m_Z     (* Gay and Nagarajan had mYi *)
  | 3 -> m_Y     (* Gay and Nagarajan had m_Z *)
  | i -> raise (Error ("** Disaster: _Phi(" ^ string_of_int i ^ ")"))

let m_Cnot = make_ug [[P_1; P_0; P_0; P_0];
                      [P_0; P_1; P_0; P_0];
                      [P_0; P_0; P_0; P_1];
                      [P_0; P_0; P_1; P_0]]
                     
let m_1 = make_ug [[P_1]] (* a unit for folding *)
let m_0 = make_ug [[P_0]] (* another unit for folding *)

(* from here on down, I just assume (hope) that we are working with square matrices *)
(* maybe later that typechecking trick ... *)

let new_v n = Array.make n P_0
let new_ug n = Array.make_matrix n n P_0

let bigI n = let m = Array.make_matrix n n P_0 in
             _for 0 1 n (fun i -> m.(i).(i) <- P_1);
             m
             
let tensor_vv vA vB =
  let nA = vsize vA in
  let nB = vsize vB in
  let vR = new_v (nA*nB) in
  _for 0 1 nA (fun i -> _for 0 1 nB (fun j -> vR.(i*nB+j) <- prod vA.(i) vB.(j)));
  if !verbose_qcalc then Printf.printf "%s (><) %s -> %s\n"
                                       (string_of_probvec vA)
                                       (string_of_probvec vB)
                                       (string_of_probvec vR);
  vR
  
let tensor_mm mA mB =
  if !verbose_qcalc then Printf.printf "tensor_mm%s%s = " (string_of_matrix mA) (string_of_matrix mB);
  let nA = msize mA in
  let nB = msize mB in
  let mt = new_ug (nA*nB) in
  _for 0 1 nA (fun i -> 
                 _for 0 1 nA (fun j -> 
                                let aij = mA.(i).(j) in
                                _for 0 1 nB (fun m ->
                                               _for 0 1 nB (fun p ->
                                                              mt.(i*nB+m).(j*nB+p) <- prod aij (mB.(m).(p))
                                                           )
                                            )
                             )
              );
   if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix mt);
   mt
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix mt);
  mt

let mult_mv m v =
  if !verbose_qcalc then Printf.printf "mult_mv%s%s = " (string_of_matrix m) (string_of_probvec v);
  let n = Array.length v in
  if msize m <> n then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_mv %s %s"
                                 (string_of_matrix m)
                                 (string_of_probvec v)
                 )
          );
  let v' = new_v n in
  _for 0 1 n (fun i -> 
                v'.(i) <- _for_rightfold 0 1 n (fun j -> sum (prod m.(i).(j) v.(j))) P_0
             );
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_probvec v');
  v'

let mult_mm mA mB =
  if !verbose_qcalc then Printf.printf "mult_mm%s%s = " (string_of_matrix mA) (string_of_matrix mB);
  let n = msize mA in
  let m = vsize mA.(0) in (* mA is n*m; mB must be m*p *)
  if m <> msize mB then
    raise (Error (Printf.sprintf "** Disaster (size mismatch): mult_mm %s %s"
                                 (string_of_matrix mA)
                                 (string_of_matrix mB)
                 )
          );
  let p = vsize mB.(0) in
  let m' = new_ug m in
  _for 0 1 n (fun i ->
                (_for 0 1 p (fun j ->
                               m'.(i).(j) <- _for_rightfold 0 1 m (fun k -> sum (prod mA.(i).(k) mB.(k).(j))) P_0
                            )
                )
             );
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix m');
  m'

let cjtrans_m m = (* square matrices only *)
  if !verbose_qcalc then Printf.printf "cjtrans_m%s = " (string_of_matrix m);
  let n = msize m in
  if n <> vsize m.(0) then
    raise (Error (Printf.sprintf "** Disaster (unsquareness): cjtrans_m %s"
                                 (string_of_matrix m)
                 )
          );
  let m' = new_ug n in
  _for 0 1 n (fun i ->
                _for 0 1 n (fun j -> m'.(i).(j) = m.(j).(i))
                _for 0 1 n (fun j -> m'.(i).(j) <- m.(j).(i))
             );
  if !verbose_qcalc then Printf.printf "%s\n" (string_of_matrix m');
  m'
  
let m_IH = tensor_mm m_I m_H
let m_HI = tensor_mm m_H m_I

type ugv =
  | GateH
  | GateFG
  | GateI
  | GateX
  | GateY
  | GateZ
  | GateCnot
  | GatePhi of int

let string_of_ugv = function
  | GateH           -> "_H"
  | GateFG          -> "_FG"
  | GateI           -> "_I"
  | GateX           -> "_X"
  | GateY           -> "_Y"
  | GateZ           -> "_Z"
  | GateCnot        -> "_Cnot"
  | GatePhi (i)     -> "_Phi(" ^ string_of_int i ^ ")"

let matrix_of_ugv = function
  | GateH           -> m_H
  | GateFG          -> m_FG
  | GateI           -> m_I
  | GateX           -> m_X
  | GateY           -> m_Y
  | GateZ           -> m_Z
  | GateCnot        -> m_Cnot
  | GatePhi (i)     -> m_Phi(i)

let arity_of_ugv = function
  | GateH           
  | GateFG          
  | GateI           
  | GateX           
  | GateY           
  | GateZ           
  | GatePhi _       -> 1
  | GateCnot        -> 2

let idx q qs = 
  let rec f i = function
    | q'::qs -> if q = q' then i else f (i+1) qs
    | []     -> raise (Error (Printf.sprintf "** Disaster: %s not in (%s)" 
                                             (string_of_qbit q) 
                                             (string_of_list string_of_qbit "," qs)
                 
                             )
                      )
  in
  f 0 qs

let bitmask iq qs = 1 lsl (List.length qs-iq-1)

let ibit q qs = (* a single-bit mask to pick out q from qs *)
  let iq = idx q qs in
  bitmask iq qs

let mask n = (* an n-bit mask *)
  let rec f m i =
    if i=0 then m else f ((m lsl 1) lor 1) (i-1)
  in
  f 0 n

let make_first qs v iq =
  let nqs = List.length qs in
  let nv = vsize v in
  let imask = bitmask iq qs in
  let i0 = bitmask 0 qs in
  let lmask = (mask iq) lsl (nqs-iq) in
  let rmask = mask (nqs-iq-1) in
  (* if !verbose || !verbose_qsim then Printf.printf "iq %d i0 %d lmask %d rmask %d\n" iq i0 lmask rmask; *)
  let v' = Array.copy v in
  for i=0 to nv-1 do
    let j = ((i land lmask) lsr 1) lor (i land rmask) lor (if i land imask<>0 then i0 else 0) in
    (* if !verbose || !verbose_qsim then Printf.printf "v'.(%d) <- v.(%d)\n" j i; *)
    v'.(j) <- v.(i)
  done;
  let seg1 = take iq qs in
  let seg2 = drop iq qs in
  let qs' = List.hd seg2 :: (seg1 @ List.tl seg2) in
  qs', v'

let rotate_left qs v = make_first qs v (List.length qs - 1)

let try_split qs v =
  let nqs = List.length qs in
  let nvs = Array.length v in
  let nzs = _for_leftfold 0 1 nvs (fun i nzs -> if v.(i)=P_0 then nzs+1 else nzs) 0 in
  let worth_a_try = nzs*2>=nvs in (* and I could do stuff with +, - as well ... *)
  let rec t_s i qs v = 
    if i=nqs then None 
    else
      (if !verbose_qcalc then 
         Printf.printf "t_s %s\n" (string_of_qval (qs,v));
       let n = vsize v in
       let nh = vsize v / 2 in
       (* if the first half is all zeros then use v_1, which is 0+1 *)
       if _for_all 0 1 nh (fun i -> v.(i)=P_0) then
         Some (qs, Array.copy v_1, Array.init nh (fun i -> v.(nh+i)))
       else
       (* if the second half is all zeros then use v_0, which is 1+0 *)
       if _for_all nh 1 n (fun i -> v.(i)=P_0) then
         Some (qs, Array.copy v_0, Array.init nh (fun i -> v.(i)))
       else
         (let qs, v = rotate_left qs v in 
          t_s (i+1) qs v
         )
      )
  in
  let r = if worth_a_try then t_s 0 qs v else None in
  if !verbose_qcalc then
    Printf.printf "try_split %s (nzs=%d, nvs=%d, worth_a_try=%B) => %s\n" 
                  (string_of_probvec v)
                  nzs nvs worth_a_try
                  (string_of_option (string_of_triple (bracketed_string_of_list string_of_qbit)
                                                      string_of_probvec 
                                                      string_of_probvec 
                                                      ","
                                    )
                                    r
                  );
  r
  
let rec record ((qs, vq) as qv) =
   let accept q = if !verbose || !verbose_qsim then
                    Printf.printf "recording %s|->%s\n" (string_of_qbit q) (string_of_qval qv);
                  Hashtbl.replace qstate q qv 
   in
   match qs with
   | []     -> raise (Error (Printf.sprintf "record gets %s" (string_of_qval qv)))
   | [q]    -> accept q
   | _'     -> (* try to split it up *)
               match try_split qs vq with
               | Some (q'::qs',vq,v') -> record ([q'], vq); record (qs', v')
               | _                    -> List.iter accept qs

let ugstep_1 id_string q (qs, v) m m' =
  let nqs = List.length qs in
  let i = idx q qs in
  let m_op =
    if i=0 && nqs=1 then m 
    else (let pre_m = _for_leftfold 0 1 i (fun _ m's -> tensor_mm m' m's) m_1 in
          let post_m = _for_leftfold (i+1) 1 nqs (fun _ m's -> tensor_mm m' m's) m_1 in
          let m_op = tensor_mm (tensor_mm pre_m m) post_m in
          if !verbose_qcalc then
            Printf.printf "pre_m = %s, m= %s, post_m = %s, m_op = %s\n" 
                          (string_of_matrix pre_m)
                          (string_of_matrix m)
                          (string_of_matrix post_m)
                          (string_of_matrix m_op);
           m_op
          )
  in
  let v' = mult_mv m_op v in
  if !verbose || !verbose_qsim then 
    Printf.printf "%s : was %s|->%s; now %s->%s\n"
                  (id_string ())
                  (string_of_qbit q)
                  (string_of_qval (qs, v))
                  (string_of_qbit q)
                  (string_of_qval (qs, v'));
  record (qs,v')

let qval_combine q1 q2 = 
  let qv1, qv2 = qval q1, qval q2 in 
  let q1s,v1 = qv1 in
  let q2s,v2 = qv2 in
  (* q1s and q2s are either identical or disjoint. *)
  let qs',v' = if qv1=qv2 then q1s,v1 else q1s @ q2s, tensor_vv v1 v2 in
  qs',v'
  
let ugstep pn qs ugv = 
  let id_string () = Printf.sprintf (if List.length qs = 1 then "%s ugstep %s >> %s" else "%s ugstep [%s] >> %s")
                                    (Name.string_of_name pn)
                                    (string_of_list string_of_qbit ";" qs)
                                    (string_of_ugv ugv)
  in
  (* let noway s = Printf.printf "can't yet handle %s %s\n" (id_string ()) s in *)

  let doit_Cnot q1 q2 =
    if q1=q2 then raise (Error (Printf.sprintf "** Disaster (same qbit twice in Cnot) %s" (id_string ())));
    let qs, v = qval_combine q1 q2 in
    let bit1 = ibit q1 qs in
    let bit2 = ibit q2 qs in
    let m_Cnot = bigI (vsize v) in
    if !verbose_qcalc then
      Printf.printf "bit1=%d, bit2=%d\n" bit1 bit2;
    Array.iteri (fun i r -> if (i land bit1)<>0 && (i land bit2)=0 then 
                                (let i' = i lor bit2 in
                                 if !verbose_qcalc then 
                                   Printf.printf "swapping rows %d and %d\n" i i';
                                 let temp = m_Cnot.(i) in
                                 m_Cnot.(i) <- m_Cnot.(i');
                                 m_Cnot.(i') <- temp
                                )
                 ) m_Cnot;
    if !verbose_qcalc then
      Printf.printf "m_Cnot = %s\n" (string_of_matrix m_Cnot);
    let v' = mult_mv m_Cnot v in
    let qv = qs, v' in
    if !verbose || !verbose_qsim then 
      Printf.printf "%s : %s|->%s; %s|->%s; now %s,%s|->%s\n"
                    (id_string ())
                    (string_of_qbit q1)
                    (string_of_qval (qval q1))
                    (string_of_qbit q2)
                    (string_of_qval (qval q2))
                    (string_of_qbit q1)
                    (string_of_qbit q2)
                    (string_of_qval qv);
    record qv
  in
  match qs, ugv with
  | [q]    , GateH       
  | [q]    , GateI      
  | [q]    , GateX      
  | [q]    , GateY      
  | [q]    , GateZ      
  | [q]    , GatePhi _  -> ugstep_1 id_string q (qval q) (matrix_of_ugv ugv) m_I
  | [q1;q2], GateCnot   -> doit_Cnot q1 q2 
  | _                   -> raise (Error (Printf.sprintf "** Disaster: ugstep [%s] %s"
                                                        (string_of_list string_of_qbit ";" qs)
                                                        (string_of_ugv ugv)
                                        )
                                 )

let rec qmeasure pn ugvs q = 
  match List.filter (fun ugv -> ugv<>GateI) ugvs with
  | []          -> (* computational measure *)
      let qs, v = qval q in
      let nv = vsize v in
      let imask = ibit q qs in
      let prob = 
        _for_leftfold 0 1 nv (fun i p -> if i land imask<>0 then 
                                           sum (prod v.(i) v.(i)) p 
                                         else p
                             ) 
                             P_0 
      in
      if !verbose || !verbose_qsim then 
        Printf.printf "%s qmeasure [] %s; %s|->%s; prob |1> = %s;"
                      (Name.string_of_name pn)
                      (string_of_qbit q)
                      (string_of_qbit q)
                      (string_of_qval (qval q))
                      (string_of_prob prob);
      let guess () =
        let r = if Random.bool () then 0 else 1 in
        if !verbose || !verbose_qsim then Printf.printf " guessing %d;" r;
        r  
      in
      let r = match prob with
      | P_0    -> 0
      | P_1    -> 1
      | P_h i -> if i=0 then 1
                 else (let rg = Random.float 1.0 in
                       let rec iexp i rf = if i=0 then rf else iexp (i-1) (rf/.sqrt 2.0) in
                       let r = if iexp i 1.0 < rg then 1 else 0 in
                       if !verbose || !verbose_qsim then Printf.printf " (biased %f<%f) guessing %d;" (iexp i 1.0) rg r;
                       r
                      )
      | _     -> guess ()
      in
      (* set the relevant probs to zero, normalise *)
      _for 0 1 nv (fun i -> if (r=1 && i land imask=0) || (r=0 && i land imask<>0)
                            then v.(i) <- P_0 (* else skip *)
                  );
      let modulus = _for_leftfold 0 1 nv (fun i p -> sum (prod v.(i) v.(i)) p) P_0 in
      if !verbose_qcalc then 
        Printf.printf " (un-normalised %s modulus %s);" (string_of_qval (qs,v)) (string_of_prob modulus);
      (match modulus with
       | P_1                -> ()
       | P_h k  when k mod 2 = 0 
                            -> let n = k/2 in
                               (* multiply by 2**(n/2) *)
                               _for 0 1 (n/2) (fun _ -> _for 0 1 nv (fun i -> v.(i) <- sum v.(i) v.(i)));
                               (* and then by 1/h if n is odd *)
                               if n mod 2 = 1 then
                                 _for 0 1 nv (fun i -> v.(i) <- r2 v.(i))
       | Pprod [p1;p2] when p1=p2 
                            -> _for 0 1 nv (fun i -> v.(i) <- div v.(i) p1)
       (* at this point it _could_ be necessary to guess roots of squares. 
        * Or maybe a better solution is required ...
        *)
       | _                  -> 
           (* is there just one possibility? If so, set it to P_1. *)
           let nzs = List.map (fun p -> if p<>P_0 then 1 else 0) (Array.to_list v) in
           if List.fold_left (+) 0 nzs = 1 then
             _for 0 1 nv (fun i -> if v.(i)<>P_0 then v.(i)<-P_1)
           else
             (if !verbose || !verbose_qsim then
                Printf.printf " oh dear!\n"; 
              raise (Error (Printf.sprintf "can't guess sqrt(%s)" 
                                           (string_of_prob modulus)
                           )
                    )
             ) 
      );
      let qv = qs, v in
      if !verbose || !verbose_qsim then 
        Printf.printf " result %d and %s|->%s\n" r (string_of_qbit q) (string_of_qval qv);
      if q=List.hd qs then record qv
      else (let nqs = List.length qs in
            let iq = idx q qs in
            let i0 = ibit (List.hd qs) qs in
            let lmask = (mask iq) lsl (nqs-iq) in
            let rmask = mask (nqs-iq-1) in
            if !verbose || !verbose_qsim then Printf.printf "iq %d i0 %d lmask %d rmask %d\n" iq i0 lmask rmask;
            let v' = Array.copy v in
            for i=0 to nv-1 do
              let j = ((i land lmask) lsr 1) lor (i land rmask) lor (if i land imask<>0 then i0 else 0) in
              if !verbose || !verbose_qsim then Printf.printf "v'.(%d) <- v.(%d)\n" j i;
              v'.(j) <- v.(i)
            done;
            let ne q' = q<>q' in
            let qs' = q :: (takewhile ne qs @ List.tl (dropwhile ne qs)) in
            let qv' = qs',v' in
            if !verbose || !verbose_qsim then Printf.printf "%s => %s\n" (string_of_qval qv) (string_of_qval qv');
            record qv'
           );
      r
  | _ -> (* in gate-defined basis *)
      if List.exists (fun ugv -> arity_of_ugv ugv <> 1) ugvs then 
        raise (Error (Printf.sprintf "** Disaster: (arity) qmeasure %s %s %s"
                                     pn
                                     (bracketed_string_of_list string_of_ugv ugvs)
                                     (string_of_qbit q)
                     )
              );
      let gs = List.map matrix_of_ugv ugvs in
      let gate = match gs with 
                 | [g]   -> g
                 | g::gs -> List.fold_left mult_mm g gs
                 | []    -> m_I (* shut up compiler -- can't happen *)
      in
      let id_string () = Printf.sprintf "rotation from %s qmeasure %s =? %s (%s)"
                                        (Name.string_of_name pn)
                                        (string_of_qbit q)
                                        (bracketed_string_of_list string_of_ugv ugvs)
                                        (string_of_matrix gate)
      let id_string gate () = Printf.sprintf "rotation from %s qmeasure %s =? %s (%s)"
                                             (Name.string_of_name pn)
                                             (string_of_qbit q)
                                             (bracketed_string_of_list string_of_ugv ugvs)
                                             (string_of_matrix gate)
      in
      let qv = qval q in
      ugstep_1 id_string q qv gate gate; 
      ugstep_1 (id_string gate) q qv gate gate; 
      let bit = qmeasure pn [] q in
      (* that _must_ have broken any entanglement: rotate the parts back separately *)
      let gate' = cjtrans_m gate in  (* transposed gate because it's unitary *)
      let qs, _ = qv in
      let qs' = List.filter (fun q' -> q'<>q) qs in
      (match qs' with
       | []    -> () (* there was only one bit *)
       | q'::_ -> (let qv' = qval q' in
                   if List.length (fst qv')<>List.length qs' then
                     raise (Error (Printf.sprintf "** Disaster: qmeasure %s %s %s: after measuring %s->%s, %s->%s"
                                                  pn
                                                  (bracketed_string_of_list string_of_ugv ugvs)
                                                  (string_of_qbit q)
                                                  (string_of_qbit q)
                                                  (string_of_qval (qval q))
                                                  (string_of_qbit q')
                                                  (string_of_qval (qval q'))
                                  )
                           );
                   ugstep_1 id_string q' qv' gate' gate'
                   ugstep_1 (id_string gate') q' qv' gate' gate'
                  )
      ); 
      ugstep_1 id_string q (qval q) gate' gate';
      ugstep_1 (id_string gate') q (qval q) gate' gate';
      bit
