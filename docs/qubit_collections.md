# Can we have indexable collections of qbits?

Yes and we've got them. Their use has to be *very* restricted. Essentially a collection is a unitary resource which has to be created together, disposed together[^1], measured together.

[^1]: This needs a new channel (*disposes*?), which isn't implemented yet.

We have to be able to construct qbit collections, index them, measure them, dispose them, print out their values ...

There is a mechanism now which allows 

  * creation of a collection, with `(newqs qs=K)` rather than `newq`. The type of the collection is `qbits` (note the s); initialisation of the constructed collection can't be omitted; and the size of the ket value `K` determines the size of the collection.  
  * gating of a collection, with `>>>` rather than `>>`.  
  * measurement of a collection, with ⌢⃫ rather than ⌢̸. The result of measurement binds a bit list. 
  * indexing of a collection, with `qs↓E`. An element of a collection can be used in a gating step, but if you use it in a measurement you lose the whole collection. (Maybe I should disallow measurement of collection elements ...).  
  * joining of two or more collections, with `(joinqs qs`<sub>`1`</sub>` , ... , qs`<sub>`n`</sub>` → qs)`. Each of the `qs`<sub>`i`</sub> is the name of a collection; the right-hand `qs` denotes the concatenation of the collections on the left; each of the left-hand `qs`<sub>`i`</sub> is used up, as if sent away or measured.  
  * splitting a collection, with `(splitqs qs → qs`<sub>`1`</sub>`(k`<sub>`1`</sub>`), ... , qs`<sub>`k`</sub>`(k`<sub>`n`</sub>`))`. Each of the `qs`<sub>`i`</sub> is the name of a new qbit collection; each of the `k`<sub>`i`</sub> is the length of that collection; the final `k`<sub>`i`</sub> is optional. The collection `qs` is split into parts of the lengths described, and disappears.
  * diagnostic-printing a collection, which uses the library function *qvals*: *qbits* &rarr; *qstate* and the channel `outq`.


  
## The need for collections

I had (still have) various Grover*n* examples which used library calls `groverG n` and `groverU bs` to generate the two component matrices of the Grover iteration. Those library functions no longer exist, but here's an example which uses matrix manipulation in the qtpi language and five explicit qbits to do Grover 5:

    fun groverG n = engate ((sx_1+sx_1)*((|+>⊗⊗n)*(<+|⊗⊗n))-(degate I⊗⊗n))

    groverU bs = engate (tabulate_diag_m (2**n) tf
                             where n = length bs
                             where tf i = if i=address then -sx_1 else sx_1
                             where address = bits2num (rev bs) (* big-endian *)  
                        )

    proc 
      System () =
        . (newq q0 = |+>)  
        . (newq q1 = |+>)
        . (newq q2 = |+>)
        . (newq q3 = |+>)
        . (newq q4 = |+>)
        .
        . (let n = 5)
        . (let G = groverG n)
        . (let bs = randbits n)
        . (let U = groverU bs)
        . (let GU = G*U)
        . (let iters = floor (pi*sqrt(2**n)/4+0.5))
        . ⁁1
        . Grover (iters, GU, q0, q1, q2, q3, q4, bs)
  
                      with 1: out!["grover 5  bs = "; show bs; "; "; show iters; " iterations"; "\n"] . _0

      Grover (iters, GU, q0, q1, q2, q3, q4, bs) =
        if iters=0 then
          . q0-/-(b0) . q1-/-(b1) . q2-/-(b2) . q3-/-(b3) . q4-/-(b4) 
          . ⁁1
          . _0
        else
          . q0,q1,q2,q3,q4>>GU
          . Grover (iters-1, GU, q0, q1, q2, q3, q4, bs)
  
                      with
                        1: . out!["measurement says "; show [b0;b1;b2;b3;b4]; 
                                  if [b0;b1;b2;b3;b4]=bs then " ok" else " ** WRONG **"; "\n"] 
                           . _0

In this context the `groverG` and `groverU` functions needn't detain us, because they only work with classical values -- matrices, gates, kets and bras. The `System` and `Grover` processes do the work, but they work with multiple single qbits, and the example is therefore tied to the number 5.

Here's an example which uses qbit collections to do the same job (I've omitted the supporting functions, and it gates with G and U separately, because it turns out to be faster):

    proc 
      System () =
        . (let n = read_min_int 1 "number of bits")
        . (newqs qs = |+>⊗⊗n)  
        .
        . (let G = groverG n)
        . (let bs = randbits n)
        . (let U = groverU bs)
        . (let iters = floor (pi*sqrt(2**n)/4+0.5))
        . ⁁1
        . Grover (iters, G, U, qs, bs)
  
                      with 1: out!["grover "; show n; " bs = "; show bs; "; "; show iters; " iterations"; "\n"] . _0

      Grover (iters, G, U, qs, secretbs) =
        if iters=0 then
          . qs⌢⃫(bs) 
          . ⁁1
          . _0
        else
          . qs>>>U . qs>>>G
          . Grover (iters-1, GU, qs, secretbs)
  
                      with
                        1: . out!["measurement says "; show bs; 
                                  if bs=secretbs then " ok" else " ** WRONG **"; "\n"] 
                           . _0

`System` asks for the number of qbits to use, generates a collection that size (the ket `|+>⊗⊗n` is `|+>⊗|+>⊗...*|+>`, with 2<sup>*n*</sup> elements). Instead of passing `Grover` *n* qbits, it gives the collection; `Grover` gates the collection the relevant number of times, then measures the whole thing. 

It's all fairly natural, but it took a while to realise that you can have and do need collection versions of creation, measurement and gating.

## The need for indexable collections

Here's a simulation of an 8-way quantum election protocol, which sets up 8 qbits in the W state (entangled so that only one of the 8 can be measured as 1) and then measures them. It uses multiple single qubits:

    proc W1q (c1) = (newq q=|1>) c1!q . _0

    proc W2q (c2) =
      (new c1)
      | W1q (c1)
      | . c1?(q0)
        . (newq q1=|0>, anc=|+>)
        . anc,q0,q1>>F . 
        . q1,anc>>CNot . 
        . c2!q0 . c2!q1 . dispose!anc
        . _0
                
    proc W4q (c4) =
     (new c2)
     | W2q (c2)
     | . c2?(q0) 
       . c2?(q1)
       . (newq q2=|0>, q3=|0>, anc=|+>)
       . anc,q0,q2>>F . 
       . anc,q1,q3>>F . 
       . q2,anc>>CNot . 
       . q3,anc>>CNot . 
       . c4!q0 . c4!q1 . c4!q2 . c4!q3 . dispose!anc
       . _0

    proc W8q (c8) =
     (new c4)
     | W4q (c4)
     | . c4?(q0) 
       . c4?(q1)
       . c4?(q2)
       . c4?(q3)
       . (newq q4=|0>, q5=|0>, q6=|0>, q7=|0>, anc=|+>)
       . anc,q0,q4>>F . 
       . anc,q1,q5>>F . 
       . anc,q2,q6>>F . 
       . anc,q3,q7>>F . 
       . q4,anc>>CNot . 
       . q5,anc>>CNot . 
       . q6,anc>>CNot . 
       . q7,anc>>CNot . 
       . c8!q0 . c8!q1 . c8!q2 . c8!q3 . c8!q4 . c8!q5 . c8!q6 . c8!q7 . dispose!anc
       . _0

    proc System () =
      . (new qc, bc)
      | W8q (qc)
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | qc?(q) . q-/-(b) . bc!b . _0
      | bc?(b0) . bc?(b1) . bc?(b2) . bc?(b3) . bc?(b4) . bc?(b5) . bc?(b6) . bc?(b7) 
        . out!["elected "; show [b0;b1;b2;b3;b4;b5;b6;b7]; "\n"] . _0
            
The `System` process invokes `W8q(qc)` which prepares 8 qbits in the W state, then sends them out serially (could be parallel) on the `qc` channel. In parallel with that System sets up 8 processes, each receiving one qbit on `qc`, measuring it and sending the measurement result on `bc`. In parallel with all that it receives those 8 messages, each 1 or 0, and prints out the result as a list. The result is always a list of all 0s except for a single 1, because of the properties of the W state.

The work is all in the `W?q` processes. The technique is taken from [the Q\# Kata on superposition](https://github.com/microsoft/QuantumKatas/blob/master/Superposition/ReferenceImplementation.qs), task 16, *WState_PowerOfTwo_Reference*. To make 2<sup>*k*</sup> qbits in the W state, make 2<sup>*k*-1</sup> in the W state and 2<sup>*k*-1</sup> |0>s, then use the F (Fredkin, CSwap) gate and CNot to combine the two halves. 

The illustrated mechanism works for numbers of qbits which are a power of 2. It is possible to make a number between 2<sup>*k*-1</sup> and 2<sup>*k*</sup> of qbits by measuring the surplus qbits: if they are all 0 then job done; if any of them is 1 then start again. (Terminates with probability 1, but would be a bit slow, I imagine, if you wanted to make W 17: you'd have to measure 15 superfluous bits and hope that you get all 0s; could take a while.) 

Neither of those mechanisms is nicely expressed in qtpi, though they can of course be done for any particular number of qbits (one algorithm per number). To do so in general -- one algorithm for any number of qbits -- obviously requires an indexable collection of qbits, and it turns out needs also joining and splitting of collections. It's much much easier to read if it uses an iteration mechanism. 

# With indexable joinable qbit collections

    fun ixs k = tabulate k (λ i. i)

    proc W (c,n) = 
      if   n<=0 then (let _ = abandon ["W "; show n; " is impossible"]) . _0
      elsf n=1  then (newqs qs = |1>) c!qs . _0
      else . (let k = floor (n/2)) 
           . (new c1) 
           | W (c1,k)     
           | . c1?(q0s)      
             . (newqs q1s = |0>⊗⊗(n-k))   
             . (newq anc = |+>)        
             . 𝄆 i←ixs k: anc,q0s↓i,q1s↓i>>F . out!["."] . _0
             . 𝄆 i←ixs k: q1s↓i,anc>>CNot . out!["."] . _0 
             . dispose!anc
             . (joinqs q0s, q1s → qs)
             . c!qs
             . _0

    proc System () =
      . (new c)
      . (let n = read_num "how many qbits") 
      | W (c,n)
      | . c?(qs)
        . out!["W "; show n; " = "] . outq!qvals qs . out!["\n"]
        . _0

W is given a channel c and a number n, assumed to be a power of 2. If n is negative then abandon the attempt; if n is non-integral it will crash in the `|0>⊗⊗(n-k)` calculation, but unfortunately without a sensible error message.

If n is 1 then it produces a 1-qbit collection initialised to `|1>`, using newqs rather than newq. 

Otherwise recurse to obtain the W n/2 state (being careful not to stray into non-integral territory), and make another collection, same size, initialised to `|0...0>`, of n-k qbits. (When I was writing it I thought it would crash if I used n-k and it wasn't a power of 2, but of course it won't, but it will crash if n isn't integral). Then do the algorithmic magic with the F and CNot gates.

Finally join the two collections into one, and send it as the result. Sample result:

        how many qbits? 8
        W 8 = [#0;#1;#2;#3;#4;#5;#6;#7]:[#2;#6;#1;#5;#0;#4;#3;#7]
                (h(3)|00000001>+h(3)|00000010>+h(3)|00000100>+
                 h(3)|00001000>+h(3)|00010000>+h(3)|00100000>+
                 h(3)|01000000>+h(3)|10000000>)

You won't get the W state if you ask for a number of qbits which isn't a power of 2, but you will get n qbits.

        how many qbits? 5
        W 5 = [#0;#1;#2;#3;#4]:[#0;#2;#1;#3;#4](h(2)|00010>+h(2)|00100>+h(2)|01000>+h(2)|10000>)

# W for odd numbers of qbits

    fun powerceiling b n =
      pwc 1
      where pwc c = if c>=n then c else pwc (b*c)
    
    proc Wmake (c,n) =
      (let k = powerceiling 2 n)
      | W (c,k)
      | . c?(qs)
        . out!["W "; show k; " = "] . outq!qvals qs . out!["\n"]
        . if k=n then _0
          else 
            . out!["discarding "; show (k-n); " qubits "]
            . (splitqs qs → q0s(k-n),qs)
            . q0s⌢⃫(bs)
            . out!["which measured "; show bs; ", leaving "] . outq!qvals qs 
            . if forall (λ b . b=0b0) bs then out!["\n"] . _0 else out![" -- round again!\n"] . Wmake (c,n)  

Richard Bornat
2022/03/15

  
