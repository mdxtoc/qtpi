# Can we have indexable collections of qbits?

Yes we can, if we proceed with care. Their use has to be *very* restricted.

## The need for indexable collections

Here's a simulation of an 8-way quantum election protocol, which sets up 8 qbits in the W state (entangled so that only one of the 8 can be measured as 1) and then measures them:

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

The illustrated mechanism works for numbers of qbits which are a power of 2. It is possible to make a number between 2<sup>*k*-1</sup> and 2<sup>*k*</sup> of qbits by measuring the surplus qbits: if they are all 0 then job done; if any of them is 1 then start again. 

Neither of those mechanisms is nicely expressed in qtpi, though they can of course be done for any particular number of qbits (one algorithm per number). To do so in general -- one algorithm for any number of qbits -- would require an indexable collection of qbits, which we don't have. If we had such collections, though, it might be possible to express parallel processing of the qbits in such a collection, rather than explicitly listing the separate processes as in `System` above.

## a first attempt

        proc W(n,c) =
          if n=1 then (newq q = |1>) c!q . _0
          else . (let k = powerceiling 2 n)
               . (new c')
               . | W(k/2, c')
                 | . c'?(lefts)
                   . -- somehow make k/2 qbits, all |0>. #Tabulate?
                   . (newq anc = |+>)
                   . #Iter (i) (anc,lefts@i,rights@i>>Cswap . _0) [0..k/2-1]
                   . #Iter (i) (rights@i,anc>>Cnot . _0) [0..k/2-1]
                   . dispose!anc
                   . (join lefts, rights as qs)             -- now lefts, rights are dead
                   . (take n from qs giving ws, rest)       -- now qs is dead
                   . -- somehow read each of rest. #Tabulate?
                   . if forall (= 0b0) bs then c!ws . _0 else W(n,c) (* infinite recursion; terminates prob 1 *)
                                                            -- should dispose ws. #Iter? #Par?

        fun powerceiling b n =
          pwc 1
          where pwc c = if c>=n then c else pwc (b*c)

-- but much to be invented yet.

Richard Bornat
2020/01/14

  
