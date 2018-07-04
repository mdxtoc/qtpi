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

exception Error of string

type qbit = int

type prob = 
  | P_0
  | P_1
  | P_i                     (* sqrt -1 *)
  | P_rh of int             (* (sqrt 1/2)**n *)
  | Prand of bool * qbit    (* if true a, otherwise b, both random unknowns s.t. a**2+b**2 = 1 *)
  | Pneg of prob
  | Pprod of prob*prob
  | Psum of prob*prob
  | Pdiff of prob*prob

type qval = qbit list * prob array (* 2^n probs in the array *)

let string_of_qbit = string_of_int

let short_string_of_qbit = string_of_int

let rec string_of_prob p = 
  let prio = function
    | P_0
    | P_1
    | P_i             
    | P_rh  _ 
    | Prand _         -> Expr.NonAssoc, 10
    | Pneg  _         -> Expr.NonAssoc,  8
    | Pprod _         -> Expr.Assoc   ,  6
    | Psum  _         -> Expr.Assoc   ,  4
    | Pdiff _         -> Expr.Left    ,  4
  in
  let binary p1 p2 op =
    let _, supprio = prio p in
    let lassoc, lprio = prio p1 in
    let rassoc, rprio = prio p2 in
    let s1 = string_of_prob p1 in
    let s2 = string_of_prob p2 in
    let s1 = if lprio<supprio || (lprio=supprio && lassoc=Expr.Right) then "(" ^ s1 ^ ")" else s1 in
    let s2 = if rprio<supprio || (rprio=supprio && rassoc=Expr.Left) then "(" ^ s2 ^ ")" else s2 in
    s1 ^ op ^ s2
  in
  match p with
  | P_0             -> "0"
  | P_1             -> "1"
  | P_rh 1          -> "rh"
  | P_rh n          -> Printf.sprintf "rh(%d)" n
  | P_i             -> "i"
  | Prand (b,q)     -> Printf.sprintf "%s(%s)" (if b then "a" else "b") (string_of_qbit q)
  | Pneg p'         -> let s = string_of_prob p' in
                       let _, supprio = prio p in
                       let _, subprio = prio p' in
                       if subprio<supprio then "-(" ^ s ^ ")" else "-" ^ s
  | Pprod (p1,p2)   -> binary p1 p2 "*"
  | Psum  (p1,p2)   -> binary p1 p2 "+"    
  | Pdiff (p1,p2)   -> binary p1 p2 "-"

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

let newqbit = (* hide the reference *)
  (let qbitcount = ref 0 in
   let newqbit () = 
     let q = !qbitcount in 
     qbitcount := !qbitcount+1; 
     let vec = Array.init 2 (fun i -> Prand (i=0, q)) in
     Hashtbl.add qstate q ([q],vec);
     q
   in
   newqbit
  )

let rec is_pconst = function
    | P_0
    | P_1
    | P_rh _
    | P_i             
    | Prand _         -> true
    | Pneg  _         
    | Pprod _         
    | Psum  _         
    | Pdiff _         -> false

let rec neg p =
  let r = match p with
          | Pneg p        -> p
          | P_0           -> p
          | Pdiff (p1,p2) -> diff p2 p1
          | _             -> Pneg p
  in
  if !verbose_simplify then
    Printf.printf "neg (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r
    
and prod p1 p2 =
  let r = match p1, p2 with
          | P_0      , _            -> P_0
          | _        , P_0          -> P_0
          | P_1      , _            -> p2
          | _        , P_1          -> p1
          | P_rh i   , P_rh j       -> rhalf (i+j)
          | P_i      , P_i          -> neg P_1
          | Pneg (p1), _            -> neg (prod p1 p2)
          | _        , Pneg (p2)    -> neg (prod p1 p2)
          | _        , Psum  _ 
          | _        , Pdiff _ 
              when is_pconst p1     -> distrib (prod p1) p2
          | Psum  _  , _        
          | Pdiff _  , _       
              when is_pconst p2     -> distrib (fun p -> prod p p2) p1
          | _ when not (is_pconst p1)
                && is_pconst p2     -> prod p2 p1
          | _                       -> Pprod (p1,p2)
  in
  if !verbose_simplify then
    Printf.printf "prod (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and sum  p1 p2 = 
  let r = match p1, p2 with
          | P_0      , _         -> p2
          | _        , P_0       -> p1
          | P_rh i   , P_rh j     
              when i=j && i>=2   -> rhalf (i-2)
          | Pneg (p1), _         -> diff p2 p1
          | _        , Pneg (p2) -> diff p1 p2
          | _                    -> Psum (p1,p2)
  in
  if !verbose_simplify then
    Printf.printf "sum (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and diff p1 p2 = 
  let r = match p1, p2 with
          | P_0      , _         -> neg p2
          | _        , P_0       -> p1
          | Pneg (p1), _         -> neg (sum p1 p2)
          | _        , Pneg (p2) -> sum p1 p2
          | _ when p1=p2         -> P_0
          | _                    -> Pdiff (p1,p2)
  in
  if !verbose_simplify then
    Printf.printf "diff (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r

and rhalf i =
  let r = if i=0 then P_1 else P_rh i in
  if !verbose_simplify then
    Printf.printf "rhalf %d -> %s\n" i (string_of_prob r);
  r

and r2 p = (* multiply by sqrt 2. Happens: see normalise *)
  let r = match p with
          | P_0                 -> p
          | P_rh i when i>=1    -> rhalf (i-1)
          | Pneg p              -> neg (r2 p)
          | Pprod (p1,p2)       -> prod (r2 p1) (r2 p2)
          | Psum (p1,p2)        -> sum  (r2 p1) (r2 p2)
          | Pdiff (p1,p2)       -> diff (r2 p1) (r2 p2)
          | _                   -> raise (Error (Printf.sprintf "r2 %s" (string_of_prob p)))
  in
  if !verbose_simplify then
    Printf.printf "r2 (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r

and div p1 p2 = (* happens in normalise *)
  let r = match p1,p2 with
          | P_0, _            -> P_0
          | _ when p1=p2      -> P_1
          | Psum (p11,p12), _ -> sum (div p11 p2) (div p12 p2)
          | _                 -> raise (Error (Printf.sprintf "div (%s) (%s)" (string_of_prob p1) (string_of_prob p2)))
  in
  if !verbose_simplify then
    Printf.printf "div (%s) (%s) -> %s\n" (string_of_prob p1) (string_of_prob p2) (string_of_prob r);
  r
  
and distrib f p =
  let r = match p with
          | P_0
          | P_1
          | P_rh _
          | P_i             
          | Prand _         -> raise (Error (Printf.sprintf "distrib ?? (%s)" (string_of_prob p)))
          | Pneg  p         -> neg (f p)
          | Pprod (p1,p2)   -> prod (f p1) (f p2)         
          | Psum  (p1,p2)   -> sum  (f p1) (f p2)         
          | Pdiff (p1,p2)   -> diff (f p1) (f p2)
  in
  if !verbose_simplify then
    Printf.printf "distrib ?? (%s) -> %s\n" (string_of_prob p) (string_of_prob r);
  r
  
let make_ug rows = rows |> (List.map Array.of_list) |> (Array.of_list)

let mH  = make_ug [[P_rh 1 ; P_rh 1      ];
                   [P_rh 1 ; neg (P_rh 1)]]
let mI  = make_ug [[P_1    ; P_0         ];
                   [P_0    ; P_1         ]] 
let mX  = make_ug [[P_0    ; P_1         ];
                   [P_1    ; P_0         ]] 
let mY  = make_ug [[P_0    ; P_1         ];
                   [neg P_1; P_0         ]] 
let mYi = make_ug [[P_0    ; neg P_i     ];
                   [P_i    ; P_0         ]] 
let mZ =  make_ug [[P_1    ; P_0         ];
                   [P_0    ; neg P_1     ]] 

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
  let rec ff i v =
    if i<n then ff (i+inc) (f i v) else v
  in
  ff i v

let rec _forrf i inc n f v =
  let rec ff i v =
    if i<n then f i (ff (i+inc) v) else v
  in
  ff i v

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

let ugstep qs ugv = 
  let id_string () = Printf.sprintf "ugstep [%s] >> %s"
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
                       let m_op = tensor_m (tensor_m pre_m m) post_m in
                       if !verbose_qsim then
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
                               (id_string ())
                               (string_of_qval (qs, v))
                               (string_of_qval (qs, v'));
               let qv = qs,v' in
               List.iter (fun q -> Hashtbl.replace qstate q qv) qs;
    
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
          Printf.printf "bit1=%d, bit2=%d\n" bit1 bit2;
        Array.iteri (fun i r -> if (i land bit1)<>0 && (i land bit2)=0 then 
                                    (let i' = i lor bit2 in
                                     if !verbose_qsim then 
                                       Printf.printf "swapping rows %d and %d\n" i i';
                                     let temp = mCnot.(i) in
                                     mCnot.(i) <- mCnot.(i');
                                     mCnot.(i') <- temp
                                    )
                     ) mCnot;
        if !verbose_qsim then
          Printf.printf "mCnot = %s\n" (string_of_matrix mCnot);
        let v' = do_mv mCnot v in
        let qv = qs, v' in
        if !verbose_qsim then 
          Printf.printf "%s : %s, %s -> %s\n"
                        (id_string ())
                        (string_of_qval (qval q1))
                        (string_of_qval (qval q2))
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
  | P_rh i -> if i=0 then 1
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
  (match modulus with
   | P_1                -> ()
   | P_rh k  when k mod 2 = 0 
                        -> let n = k/2 in
                           (* multiply by 2**(n/2) *)
                           let halfn = n/2 in
                           _for 0 1 halfn (fun _ -> _for 0 1 (vsize v) (fun i -> v.(i) <- sum v.(i) v.(i)));
                           if n mod 2 = 1 then
                             _for 0 1 (vsize v) (fun i -> v.(i) <- r2 v.(i))
   | Pprod (p1,p2) when p1=p2 
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