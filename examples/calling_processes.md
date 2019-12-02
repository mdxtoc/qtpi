 # Calling processes
 
 The pi calculus is a stark language. For various reasons it is useful to define shorthands which allow subprocesses to be inserted into the body of an enclosing process. This mechanism has already allowed qtpi to have *logging* subprocesses, so that a computation description isn't obscured by commands which log process state, progress etc. It will shortly allow iterated processes as well.
 
 ## Compiling a process call
 
A pi calculus process body is more or less a straight-line sequence of steps; guarded sums allow us to choose between sequences; conditional and matches in qtpi likewise allow choice. But there's no looping, and a process terminates (`_0` in qtpi) or changes into another process by a process invocation. That invocation, unlike a conventional function call, never returns. But, given some restrictions on the shape of a process body, we can imitate call and return using process-par and a message.

Suppose process `P` has a body which always terminates with `_0`, not with a process invocation, and doesn't contain a process-par. Suppose we replace each `_0` by `c!()._0`, where `c` isn't used elsewhere in `P`, and we add `c` to `P`'s parameters. Then the construct

        ... preamble process ...
        (new c)
        | P(arguments,c)
        | c?(_) . ... continuation process ...

will invoke `P`, wait for it to signal that it has finished, and then continue with the continuation. We could use this pattern as the compiled program which corresponds to `preamble . call P(arguments) . continuation`, if it were helpful to have such a construct in qtpi's language.

## Restrictions on a called process

A called process can't end with a process invocation and can't use a process-par, else we can't insert the `c!()` steps which signal its termination to the calling process.

## Nested processes

Suppose that as well as pi-calculus processes (`proc P ...` in qtpi) we could have local processes which could use free variables of their enclosing process, just like enclosed functions in a conventional programming language. Suppose that like &lambda; for functions we have &pi; for processes. We could then call such a process. In effect its body, with arguments substituted for parameters, would replace `P(arguments,c)` in the listing above, and its body could make use naturally of any variables declared in the preamble. Note that this doesn't require anything new from the pi calculus.

This is exactly the mechanism used to implement logging in qtpi. Note that logging processes can't do more than calculate in the functional language and send on output channels, so their compilation into the program text doesn't have any effect on quantum resource. But also note that if the same logging process is called more than once, it has to be typechecked at each call.

Suppose that we were to call a nested process which could access free quantum resource (i.e. qbits and quantum collections bound before `(new c)`). What restriction should we impose on its use of that resource?

Suppose, first, a non-repeated call. Then the body of the called process is in effect sequentially after the preamble and sequentially before  the continuation. We could resource-check it as such, and if the called process measured *q*, for example, then *q* would have to be an active qbit after the preamble and couldn't be used in the continuation. Note that if we use argument substitution before resource-checking the body of the nested process, a qbit given as argument to a called process won't generate two names for the same qbit and so won't confuse the resource checker.

Suppose, second, a repeated call, where we have some way of calling the same subprocess twice. Clearly that subprocess can't measure or send away a free *q*, because the second call would then not be able to make use of it. So a subprocess which is to be iterated ought not to affect the lifetime of a free qbit or qbit collection. Otherwise it can make use of quantum resource in any way it likes.

Suppose, third, parallel invocation of two or more copies of a subprocess. Clearly the subprocess can't take a free qbit as argument (that would be cloning); clearly the subprocess can't make use of a free qbit (that would be sharing). 

So process calling seems to support a form of process iteration and a form of process parallelism, with restrictions. Iterative algorithms (some of them) are within qtpi's reach. And it would support an explicit call construct, if it were ever necessary to have one.
