---
title: What I did to Qtpi in the Lockdown (parts 1 and 1a)
---

 

###### *Richard Bornat*

###### *School of Science and Technology, Middlesex University, London, UK*

##### *R.Bornat\@mdx.ac.uk*

#### 2020/04/23

 
-

Part 1
======

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
2\*\**n* for some *n*, and unitary (*m*\**m*†=I⊗..⊗n).

 

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

 

The *groverG* function constructs `|+++>*<+++|` (a matrix of 2\*\*3 by 2\*\*3
entries, each 2\*\*(-3)), multiplies it by 2 (sx_1 is a symbolic complex number
respresenting 1) to give a matrix of 2\*\*3 by 2\*\*3 entries entries, each
2\*\*(-2). Then subtracts the diagonal matrix `I⊗I⊗I`, leaving a matrix which is
2\*\*(-2) everywhere, except on the diagonal where it is 2\*\*(-2)-1. Then the
*engate* library function checks that it is a square matrix, size 2\*\**n* for
some *n*, and unitary (*m*\**n*`†`=I⊗..⊗I), and type-converts it to a gate. The
*degate* library function is necessary to type-convert `I⊗I⊗I` from a gate to a
matrix.

The *groverU* function uses the library function `tabulate_m` to construct the
oracle matrix, which is a 2\*\*3 diagonal matrix of 1s, except that at the
'answer' position it's -1. *engate* checks that it's a proper gate.

Qtpi had until this point used a Hindley-Milner type-assignment algorithm, and
it was very rarely necessary to insert explicit types. It's still rarely
necessary, but the new typechecking algorithm nevertheless takes account of the
overloading of various operators:

 

| Operator          | types                                              |
|-------------------|----------------------------------------------------|
| unitary minus (-) | 'a → 'a for *num*, *sxnum*                         |
| \+, -             | 'a → 'a → 'a for *num*, *sxnum*, *matrix*          |
| †                 | 'a → 'a → 'a for *gate*, *matrix*                  |
| `*`               | 'a → 'a → 'a for *num*, *sxnum*, *gate*, *matrix*  |
|                   | *gate* → *ket* → *ket*                             |
|                   | *ket* → *bra* → *matrix*                           |
|                   | *bra* → *ket* → *sxnum*                            |
|                   | *sxnum* → *matrix* → *matrix*                      |
|                   | *matrix* → *sxnum* → *matrix*                      |
| ⊗                 | 'a → 'a → 'a for *bra*, *ket*, *gate*, *matrix*    |
| ⊗⊗                | 'a → *num* → 'a for *bra*, *ket*, *gate*, *matrix* |

 

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

 

The `Wmake` process makes a collection size *k* for *2\*\**(*k*-1)\<*n*⩽2\*\*k;
then, if it has made too many, separates *k*-*n* of them, measures those and if
it finds only \|0\> values, it has done the job. The technique is also from the
[Q\# github
repository](https://github.com/microsoft/QuantumKatas/blob/master/Superposition/ReferenceImplementation.qs)
(solution based on generation for 2ᵏ and post-selection using measurements).

 

Sparse vectors and matrices
---------------------------

 

All this language ingenuity is all very well (I think so, anyway), but a bit of
experience with the Grover and W examples showed that they ran slowly (Grover)
and/or ran out of space (W, and possibly Grover). The problem, a bit of
experiment with diagnostic switches such as -verbose qsim and -verbose qcalc
showed me, is tensoring of very large matrices and multiplication of large
matrices and large vectors. But in many cases -- in all the cases I was looking
at -- these matrices were very repetitive. For example, the groverG matrix is
almost all *h*\*\**n* for some *n* (where *h*=1/*sqrt*(2), and the matrices and
vectors used in the W example are almost all zeros.

### Sparsity with zeros

I made it possible (easy to say, but it took me quite some time) to have sparse
vectors and matrices where the missing entries were all zeros. One very useful
sparse matrix is I⊗⊗*n*, and I gave it special treatment: it's represented as an
OCaml function. That meant that steps like `anc,q0s↓i,q1s↓i>>F` in the W example
don't generate a large matrix representation: it's constant space. And since the
state of the qbits is also mostly zeros, the space problem goes away. (I've also
functionalised H⊗⊗*n*, which is useful when measuring in the diagonal basis, but
I haven't exploited it yet.)

But it's very tempting to try to optimise the dot product operation that's at
the heart of a gating step: the vector which represents the state of all the
qbits, size *2\*\*n,* where *n* is the number of qbits we're dealing with, is
multiplied by the matrix F⊗(I⊗⊗(*n*-3)), which means forming the dot product of
each row of the matrix with the vector, each dot product about 2*n*
multiplications, but most delivering 0. But we have a sparse vector
representation of the state: if we look at the columns of the matrix we can see
which rows are non-zero in at least one of the positions at which the state is
non-zero. It's easy to do that, given a functional representation of the matrix,
and it speeds up the gating operation no end.

Before the dot product optimisation qtpi could just about do W 16; following the
optimisation it could do W 16 and W 32 really quickly and of course I tried W 64
... which crashed.

### Addressing with large integers

The problem with the W algorithm and 64 qbits is that the matrix must be 2\^64
square, but OCaml uses 63-bit integers. My sparse tensor algorithm went wrong,
because division and remaindering by large numbers doesn't work. But no matter:
OCaml has a Z module that represents arbitrarily large integers. It was a slog
to go over to zint addressing of matrices, but it worked. I could do W 64, W
128, ... all the way to W 1024, which is a bit more than a real quantum computer
will be able to do for a decade or two. It will do more, but I got bored and the
execution times got a bit long.

### Sparsity with non-zero values

To save space in the Grover example, I had to allow sparse matrices in which the
gaps are non-zero. This, too, was a slog, and it made little difference at first
because the Grover matrices weren't very big -- large examples take too much
time -- and because I couldn't optimise the dot product, or at least I couldn't
do it as well as in the zero case. Then I realised that if I allowed negative
powers of my constant *h* (1/*sqrt*(2), remember) then I could efficiently
implement multiplication of a symbolic number by a zint. That speeded up the dot
product, but not as much as I'd hoped. Still, I can do larger Grover examples
now.

### What a lot of effort

It was a lot of work. I felt quite heroic, at the end of each of the stages.

 

Part 1a
=======

 

Sparse matrices and Grover
--------------------------

The [Grover
example](https://github.com/mdxtoc/qtpi/blob/master/examples/Grover/grover.qtp)
ran annoyingly slowly: anything over 8 qbits took minutes. And there was a long
delay before it reported the random choice of bit values and the number of
iterations. There were a number of things going on.

First, it calculated `G*U` and each iteration put the qbit collection through
that gate. But although `G` and `U` are diagonal, `G*U` isn't. That considerably
slowed my gating mechanism. Putting the collection through `U` and then `G`
speeded it up a lot, which made the initialisation delay more annoying still.

The first problem was the multiplication `(|+>⊗⊗n)*(<+|⊗⊗n)`. I hadn't optimised
the function that did the work: given that both sides are very extremely sparse
(only zero values in either vector), it should have been easy. Eventually I
worked it out.

The second problem was the *engate* function. It has to check that its argument
is a square matrix (easy) and that its size is a power of 2 (easy). Then it
computes `m*m†` and checks that it's all zeros except for a diagonal of ones.
Again, for the matrices `G` and `U` this should have been easy. Eventually I
worked out how to do matrix multiplication of sparse diagonal matrices, even
when the off-diagonal values aren't zero, and the initialisation delay dropped
from tens of seconds to tenths of a second.

Now, even Grover 13 is easily computed in about a minute.

All that sounds easier than it was ...

 

That's all, folks!
==================

 

as of today.

 

RB 2020/04/28

 
