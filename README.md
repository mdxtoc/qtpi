# qtpi: a quantum protocol simulator

(README modified 2020/01/02 because it hadn't been changed since the repository started.)

Qtpi is a simulator for a modified version of Gay and Nagarajan's CQP (Communicating Quantum Processes, POPL 2005). Still under development, but already a capable tool.

Qtpi is a mixture of two notations: there's a process language, based on the pi calculus with special steps to allow quantum bits (qubits) to be created (`newq`), put through gates (`>>`) and measured (`-/-`) -- and, inherited from CQP, it mis-spells qubit as qbit. There's also a functional language, which at present is a muddly combination of ideas from OCaml and Miranda (sorry) that enables classical calculations. There's a symbolic calculator for quantum probabilities (just matrix algebra).

The two things which make it interesting are the calculator and the static check for non-sharing / non-cloning of qubits. Qubits shouldn't be shared between protocol processes, which are supposed to be spatially separated, and they must not be cloned (aka copied) because that would violate a central theorem of quantum mechanics, believed to be a fundamental fact about the real world. CQP uses *linear typing* to make the anti-sharing / anti-cloning check. Because I misunderstood the original paper (shame!) I thought I should innovate and do it using ideas from separation logic. Which might have worked, but after thrashing around I decided to drastically restrict the use of qubits: they can't be in tuples or lists, they have to be sent singly in messages or as process arguments. That makes sense if you think of how an implementation would have to handle a photon, and since quantum protocols are implemented using photons ...

Still under development, as I said. We're currently experimenting with some simple quantum calculation examples like Grover and quantum leadership election. And I'm experimenting with iterative constructs to aid description of algorithms.

There is a [language description](https://github.com/mdxtoc/qtpi/blob/master/docs/qtpi_description.md) in the [docs directory](https://github.com/mdxtoc/qtpi/tree/master/docs), and there are examples in the [examples directory](https://github.com/mdxtoc/qtpi/tree/master/examples) -- and have a look at [the BBEdit worksheet](https://github.com/mdxtoc/qtpi/blob/master/Qtpi.worksheet) for how to run them. There are even a couple of binary releases. See [HOW\_TO\_USE.md](https://github.com/mdxtoc/qtpi/blob/master/HOW_TO_USE.md) if you want to build it yourself.

## Acknowledgements

Qtpi's internal priority queues are based on Jean-Christophe Filliatre's implementation of binary heaps, from [his github repo](https://github.com/backtracking/bheap.git). 

