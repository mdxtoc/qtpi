# qtpi: a quantum protocol symbolic checker

I have written a simulator for a modified version of Gay and Nagarajan's CQP (Communicating Quantum Processes, POPL 2005). Very much work in progress, but it already does some interesting things.

I began this work because I saw that CQP had a potential to deal with 'ownership' of qbits. When a qbit is sent from one process to another, the first must 'own' it to begin with, and the second must 'own' it afterwards. Because qtpi  has, like the pi calculus, only tail recursion and no conditional steps (though it does have conditional choice between processes), it seems likely that ownership could be dealt with by a type checker.

I haven't got around to ownership yet, because I realised that the kind of problems I was looking at didn't need efficient simulation, and I could write a symbolic quantum simulator. So that is what qtpi is at present: a parser, typechecker and quantum simulator for simple quantum protocols. Ownership type-checks will come soon, I promise.

There is a language description in the docs directory, and there are examples in the examples directory. More to come.

## Acknowledgements

Qtpi's internal priority queues are based on Jean-Christophe Filliatre's implementation of binary heaps, from [his github repo](https://github.com/backtracking/bheap.git). 

