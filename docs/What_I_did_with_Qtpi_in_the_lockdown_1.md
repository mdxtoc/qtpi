---
title: What I did to Qtpi in the Lockdown
---

 

###### *Richard Bornat*

###### *School of Science and Technology, Middlesex University, London, UK*

##### *R.Bornat\@mdx.ac.uk*

#### 2020/04/23

 
-

Background
----------

 

I'm 75, so I'm seriously locked down. It's about seven weeks since I started,
and my main distraction so far has been hacking Qtpi. I've done several things:
unicoding, introduced some new types; overloading operators, qbit collections,
iteration, and sparse vectors and matrices.

 

Unicoding
---------

 

Some of the operators in Qtpi are pretty ugly in their ASCII form, so I switched
to a lexer which can do Unicode. Here's what I have included so far. The ASCII
equivalents are still available.

 

| Symbol                | Unicode | ASCII         |
|-----------------------|---------|---------------|
| tensor product        | ⊗       | `><`          |
| tensor power          | ⊗⊗      | `><><`        |
| dagger                | †       |               |
| lambda                | λ       | `lam`         |
| process insertion     | ⁁       | `/^`          |
| repeat                | 𝄆      | `|:`          |
| end repeat (optional) | 𝄇      | `:|`          |
| measure               | ⌢̸       | `-/-`         |
| multi-measure         | ⌢⃫       | \-//-         |
| not                   | ¬       | `not`         |
| right arrow           | →       | \-\>          |
| left arrow            | ←       | \<-           |
| down arrow            | ↓       | no equivalent |

 

In place of the postfix † operator (dagger -- conjugate transpose) you can use
the `dagger_m` function. There's no equivalent of the infix ↓ (subscript --
extract element of qbit collection).

To make all this work I had to remake the lexer so that it could be processed by
OCaml's *sedlex*. I couldn't use the *menhir* parser because it's LR(1), so my
offside-parsing hack wouldn't work any more. I (lazily) used a function in
OCaml's *menhirlib* to interface the lexer to my *ocamlyacc*-generated parser.

 

New types: sxnum, bra, ket, matrix
----------------------------------

 

Qtpi's calculator uses symbolic numbers: originally symbolic reals, now symbolic
complex numbers. There is now a type sxnum of symbolic complex numbers.

It is possible to initialise a qbit with a declaration such as `(newq q=|0>)`;
the constant after the `=` used to be a `basisv` type, which had no other use.
There is now a type `bra`, and also a type `ket`.

The type `matrix` joins the type `gate`. Gates are square matrices, sized
$$2^n$$ for some $$n$$, and unitary ($$m*m†=I⊗⊗n$$).

 

| type   | constants                              |
|--------|----------------------------------------|
| sxnum  | `sx_0`, `sx_1`, `sx_h`, `sx_f`, `sx_g` |
| bra    | `|`[`01+-`]+`>`                        |
| ket    | `<`[`01+-`]+\|                         |
| matrix |                                        |

 

Overloading operators
---------------------

 

I had a version of the Grover algorithm which looked like this (I had several:
this was the version for 3 qbits).

 

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
proc 
  System () =
    . (newq q0 = |+>)  
    . (newq q1 = |+>)
    . (newq q2 = |+>)
    .
    . (let n = 3)
    . (let G = groverG n)
    . (let bs = randbits n)
    . (let U = groverU bs)
    . (let GU = G*U)
    . (let iters = floor (pi*sqrt(2**n)/4+0.5))
    . ⁁1
    . Grover (iters, GU, q0, q1, q2, bs)
  
                  with 1: out!["grover 3  bs = "; show bs; "; "; show iters; 
                                        " iterations"; "\n"] . _0

  Grover (iters, GU, q0, q1, q2, bs) =
    if iters=0 then
      . q0-/-(b0) . q1-/-(b1) . q2-/-(b2) 
      . ⁁1
      . _0
    else
      . q0,q1,q2>>GU
      . Grover (iters-1, GU, q0, q1, q2, bs)
  
                  with
                    1: . out!["measurement says "; show [b0;b1;b2]; 
                              if [b0;b1;b2]=bs then " ok" else " ** WRONG **"; 
                              "\n"] 
                       . _0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 

Note:

-   it works only for 3 qbits;

-   it uses (what were then) built-in *groverG* and *groverU* functions to build
    the matrices the algorithm needs.

 

I wanted to be able to write a program which calculated the matrices itself. I
came up with the following functions:

 

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
fun groverG n = engate ((sx_1+sx_1)*(|+++>*(<+++|)-(degate (I⊗I⊗I))

   groverU bs = engate (tabulate_m (2**n) (2**n) tf)
                 where n = length bs
                 where tf i j = if i<>j      then  sx_0 else
                                if i=address then -sx_1 else 
                                                   sx_1
                 where address = bits2num (rev bs) (* big-endian *)  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 

The *groverG* function constructs `|+++>*<+++|` (a matrix of $$2^3*2^3$$
entries, each $$2^{-3}$$), multiplies it by 2 (sx_1 is a symbolic complex number
respresenting 1) (a matrix of $$2^3*2^3$$ entries, each $$2^{-2}$$), and
subtracts the diagonal matrix `I⊗I⊗I`, leaving a matrix which is $$2^{-2}$$
everywhere, except on the diagonal where it is $$2^{-2}-1$$. Then the *engate*
library function checks that it is a square matrix, size $$2^n$$ for some $$n$$,
and unitary ($$n*n$$`†`$$=I⊗I⊗I$$), and type-converts it to a gate. The *degate*
library function is necessary to type-convert `I⊗I⊗I` from a gate to a matrix.

The *groverU* function uses the library function `tabulate_m` to construct the
oracle matrix, which is a $$2^3$$ diagonal matrix of 1s, except that at the
'answer' position it's -1. *engate* checks that it's a proper gate.

Qtpi had until this point used a Hindley-Milner type-assignment algorithm, and
it was very rarely necessary to insert explicit types. It's still rarely
necessary, but the new typechecking algorithm nevertheless takes account of the
overloading of various operators:

 

| Operator          | types                                                      |
|-------------------|------------------------------------------------------------|
| unitary minus (-) | *'a* →\* *'a for* num*,* sxnum\*                           |
| \+, -             | *'a* →\* 'a *→* 'a\* for *num*, *sxnum*, *matrix*          |
| †                 | *'a* →\* 'a *→* 'a\* for *gate*, *matrix*                  |
| `*`               | *'a* →\* 'a *→* 'a\* for *num*, *sxnum*, *gate*, *matrix*  |
|                   | *gate* →\* ket *→* ket\*                                   |
|                   | *ket* →\* bra *→* matrix\*                                 |
|                   | *bra* →\* ket *→* sxnum\*                                  |
|                   | *sxnum* →\* matrix *→* matrix\*                            |
|                   | *matrix* →\* sxnum *→* matrix\*                            |
| ⊗                 | \* 'a\* →\* 'a *→* 'a\* for *bra*, *ket*, *gate*, *matrix* |
| ⊗⊗                | *'a* → *num* →\* 'a\* for *bra*, *ket*, *gate*, *matrix*   |

 

Qbit collections
----------------

 

It's tedious to have to work with single qbits, when a algorithm such as
Grover's works with a collection of qbits, creating them all together, putting
them all through a gate, measuring them together. For this and other reasons I
introduced qbit collections, type *qbits*. In resource terms they work like
qbits: you create a single value, you can't share it, you can't clone it. But
you can measure it, in which case you get a bit list the size of the collection.

-   A collection is created by `(newqs name=ket)`; the size of the collection is
    determined by the size of the *ket* you provide. *name* is given the type
    *qbits*.

-   You gate a collection, all at once, by `name>>>gate`.

-   You measure a collection, all at once, by `name⌢⃫(bs)`in the computational
    basis, or `name⌢⃫[gate](bs)`in some other basis defined by `gate`. In either
    case the bit-list `bs` is bound to the result of measuring every qbit in the
    collection.

Here's the new Grover example, using qbit collections:

 

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
fun compose (f : 'b -> 'a) (g : 'c -> 'b) (v : 'c) : 'a = f (g v)

fun semicolon (g : 'c -> 'b) (f : 'b -> 'a) : ('c -> 'a) = compose f g

fun read_min_int m s
  = k where k = if j>=m then j 
                else semicolon (λ _ . print_strings ["pardon? at least "; show m; 
                                                        "\n"])
                               (λ _ . read_min_int m s)
                               ()
      where j = read_num s

fun groverG n = engate ((sx_1+sx_1)*((|+>⊗⊗n)*(<+|⊗⊗n))-(degate I⊗⊗n))

   groverU bs = engate (tabulate_m (2**n) (2**n) tf)
                 where n = length bs
                 where tf i j = if i<>j      then  sx_0 else
                                if i=address then -sx_1 else 
                                                   sx_1
                 where address = bits2num (rev bs) (* big-endian *)  
                 
proc 
  System () =
    . (let n = read_min_int 1 "number of bits")
    . (newqs qs = |+>⊗⊗n)  
    .
    . (let G = groverG n)
    . (let bs = randbits n)
    . (let U = groverU bs)
    . (let GU = G*U)
    . (let iters = floor (pi*sqrt(2**n)/4+0.5))
    . ⁁1
    . Grover (iters, GU, qs, bs)
  
                  with 1: out!["grover "; show n; " bs = "; show bs; "; "; 
                                    show iters; " iterations"; "\n"] . _0

  Grover (iters, GU, qs, secretbs) =
    if iters=0 then
      . qs⌢⃫(bs) 
      . ⁁1
      . _0
    else
      . qs>>>GU
      . Grover (iters-1, GU, qs, secretbs)
  
                  with
                    1: . out!["measurement says "; show bs; 
                              if bs=secretbs then " ok" else " ** WRONG **"; "\n"] 
                       . _0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 

Iteration and indexing
----------------------

 

For some time I've been developing and using iteration. Here, for example, is an
example which tests a full-adder circuit for a variety of possible inputs:

 

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
proc System () =
  𝄆 (a,b,c) ← [(|0>,|0>,|0>); (|0>,|0>,|1>); (|0>,|1>,|0>); (|0>,|1>,|1>); 
               (|1>,|0>,|0>); (|1>,|0>,|1>); (|1>,|1>,|0>); (|1>,|1>,|1>);
               (|+>,|0>,|0>); (|0>,|+>,|0>); (|0>,|0>,|+>); 
               (|+>,|+>,|0>); (|+>,|0>,|+>); (|0>,|+>,|+>);
               (|+>,|+>,|+>)] :
        (newq qA   = a, 
              qB   = b,
              qCin = c) . ⁁1 .
        (newq qSum=|0>, qCout=|0>) .
        qA,qSum>>CNot . qB,qSum>>CNot . qCin,qSum>>CNot .
        qA,qB,qCout>>T . qA,qCin,qCout>>T . qB,qCin,qCout>>T .
        ⁁2 . 
        
        (* collapse entanglements and dispose, to simplify trace *)
        qA-/-(_) . qB-/-(_) . qCin-/-(_) . 
        qSum-/-(_) . qCout-/-(_) . 
        _0
  . 
  _0
            with 1: out!["full adder sum of (A="] . outq!qval qA . out![", B="] .
                             outq!qval qB . out![", Cin="] . 
                             outq!qval qCin . out![")"] ._0
                 2: out![" is (Cout="] . outq!qval qCout . out![", sum="] .
                             outq!qval qSum . out![")\n"] . _0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 

The repeat sign 𝄆 (`|:` in ASCII) comes before a description of the values of
`(a,b,c)` which parameterise the subprocess that follows ':'. Output is provided
on each run of that subprocess by the sub-subprocesses labelled 1 and 2 that are
inserted where the insertion carets specify.

For the resource-checking (no cloning, no sharing, no use after measurement) to
work, the repeated (sub)process can't be a named process invocation. Indeed the
repeated process can't make a process invocation, can't measure any qbits or
send them away in messages. But it can gate them, and the subprocess in this
example does.

I wanted to use this mechanism to build a program which could calculate the
[generalised W state](https://en.wikipedia.org/wiki/W_state) (an entanglement in
which each state has all qbits but one in the \|0\> state, and the other in the
\|1\> state). I found an algorithm on the [Q\# github
repository](https://github.com/microsoft/QuantumKatas/blob/master/Superposition/ReferenceImplementation.qs),
but it used indexing of qbit arrays;

 

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// Task 16. W state on 2ᵏ qubits
// Input: N = 2ᵏ qubits in |0...0⟩ state.
// Goal: create a W state (https://en.wikipedia.org/wiki/W_state) on these qubits.
// W state is an equal superposition of all basis states on N qubits of Hamming weight 1.
// Example: for N = 4, W state is (|1000⟩ + |0100⟩ + |0010⟩ + |0001⟩) / 2.

operation WState_PowerOfTwo_Reference (qs : Qubit[]) : Unit is Adj {

    let N = Length(qs);
    if (N == 1) {
        // base of recursion: |1⟩
        X(qs[0]);
    } else {
        let K = N / 2;

        // create W state on the first K qubits
        WState_PowerOfTwo_Reference(qs[0 .. K - 1]);
        
        // the next K qubits are in |0...0⟩ state
        // allocate ancilla in |+⟩ state
        using (anc = Qubit()) {
            H(anc);
            for (i in 0 .. K - 1) {
                Controlled SWAP([anc], (qs[i], qs[i + K]));
            }
            for (i in K .. N - 1) {
                CNOT(qs[i], anc);
            }
        }
    }
} 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 

What if I could index a qbit collection? Well, why not? If the only thing you
are permitted to do is to gate an element of a collection (measuring an element
in resource terms would measure the lot), nothing can go wrong. This example
only gates. I have repetition already, and I invented `collectionE↓indexE` as a
syntax for indexing. I needed also to be able to join and split collections:
`(joinqs c1, c2 → c)` uses up collections `c1` and `c2` -- so they can't be used
again -- and makes a new collection `c`; `(splitqs c → c1(N), c2)` uses up
collection `c` and makes `c1` and `c2`; `c1` gets the first `N` elements of `c`
and `c2` gets the rest. It goes very nicely:

 

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
fun ixs k = tabulate k (λ i. i)

fun powerceiling b n =
  pwc 1
  where pwc c = if c>=n then c else pwc (b*c)

proc W (c,n) = 
  if   n<=0 then (let _ = abandon ["W "; show n; " is impossible"]) . _0
  elsf n=1  then (newqs qs = |1>) c!qs . _0
  else . (let k = floor (n/2)) 
       . (new c1) 
       | W (c1,k)     
       | . c1?(q0s)      
         . out!["W "; show n; " has "; show (n/2); "\n"]
         . (newqs q1s = |0>⊗⊗(n-k))   
         . (newq anc = |+>)        
         . 𝄆 i←ixs k: anc,q0s↓i,q1s↓i>>F . out!["."] . _0
         . out!["W "; show n; " has done its Fs\n"]
         . 𝄆 i←ixs k: q1s↓i,anc>>CNot . out!["."] . _0 
         . out!["W "; show n; " has done its CNots\n"]
         . dispose!anc
         . (joinqs q0s, q1s → qs)
         . c!qs
         . _0

proc Wmake (c,n) =
  (let k = powerceiling 2 n)
  | W (c,k)
  | . c?(qs)
    . out!["W "; show k; " = "] . outq!qvals qs . out!["\n"]
    . if k=n then _0
      else 
        . out!["discarding "; show (k-n); " qbits "]
        . (splitqs qs → q0s(k-n),qs)
        . q0s⌢⃫(bs)
        . out!["which measured "; show bs; ", leaving "] . outq!qvals qs 
        . if forall (λb.b=0b0) bs then out!["\n"] . _0 
                                  else out![" -- round again!\n"] . Wmake (c,n) 
              
proc System () =
  . (new c)
  . (let n = read_num "how many qbits") 
  . Wmake (c,n)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 

The `Wmake` process makes a collection size $$k$$ for $$2^{k-1}<n<=2^k$$, then
if it has made too many, separates $$k-n$$ of them, measures those and if it
finds only \|0\> values, it has done the job. The technique is also from the
[Q\# github
repository](https://github.com/microsoft/QuantumKatas/blob/master/Superposition/ReferenceImplementation.qs)
(solution based on generation for 2ᵏ and post-selection using measurements).

 

That's all, folks!
------------------

 

as of today.

 

RB 2020/04/24

 
