 # Calling nested processes (iteratively and in parallel)
 
 The pi calculus is a stark language. For various reasons it could be useful to define shorthands which allow subprocesses to be inserted into the body of an enclosing process. This mechanism has already allowed qtpi to have *logging* subprocesses, so that a computation's description isn't obscured by commands which log process state, progress etc. It will shortly allow iterated processes as well.
 
 ## A mechanism for process call
 
A pi calculus process body is more or less a straight-line sequence of steps; guarded sums allow us to choose between sequences; conditional and matches in qtpi likewise allow choice. But there's no looping, and a process terminates (`_0` in qtpi) or changes into another process by a process invocation. That invocation, unlike a conventional function call, never returns. But, given some restrictions on the shape of a process body, we can imitate call and return using process-par and a message.

Suppose process `P` has a body which always terminates with `_0`, not with a process invocation, and doesn't contain a process-par. Suppose we make a new process `Pc` by replacing each `_0` by `c!()._0`, where `c` isn't used elsewhere in `P`, and adding `c` to the parameters. Then the construct

        <preamble>
        (new c)
        | Pc(arguments,c)
        | c?(_) . <continuation>

will execute the preamble, then the body of `P`, and finally the continuation. In effect `P` is called, and returns.

Since this is just a bit of programming within the pi calculus tradition, normal qtpi resource-checking works fine: the two apparently-parallel (but really sequential) arms can't share any quantum resource. So `P` shouldn't take a qbit as argument.

We could use this pattern as the compiled program which corresponds to `preamble . call P(arguments) . continuation`, if it were helpful to have such a construct in qtpi's language.

Note that the mechanism requires that the called process `P` can't end with a process invocation (unless it's a recursive invocation of `P`) and can't use a process-par, else we can't insert the `c!()` steps which signal its termination to the calling process.

## Recursive process call

If `P` is recursive then some of its executions will invoke a new execution of itself. Change those to calls of `Pc` and we can call recursive `Pc` and the same mechanism works: `Pc` is called, and it returns. I used this mechanism to simulate BB84 QKD, for example. Alice defines a list of bases `bs` and values `vs` and sends qbits to Bob encoding those values down the previously-defined channel `qc`. (Please ignore the flagrant use of extra unnecessary separating dots in qtpi code: I'm experimenting with it to make programs easier to write and to read)

        <preamble>
      . (let bs = randbits n) 
      . (let vs = randbits n)  
      . (new sent)
      | . SendQbits (zip bs vs, qc, sent)
      | . sent?(_)
        . <continuation>

Separately I defined the called process `SendQbits`

    proc SendQbits (bvs,qc,sent) =   
        match bvs .
        + []         . sent!() . _0
        + (b,v)::bvs . (newq q = basisv_of_bits b v)
                         qc!q    .
                         SendQbits (bvs,qc,sent)

For each `(b,v)` pair, `SendQbits` makes a new qbit `q` and sends it down channel qc.

## Iterative process call

The encoding above works perfectly as an execution mechanism. But it doesn't work well as a description, because it's mostly mechanism. The `sent` channel, the argument `qc`, the `match` construct: all of it is mechanism to describe a simple process iteration. Ten lines of code in total, two of them about what's really happening.

Here's what I would prefer to write:

        <preamble>
      . (let bs = randbits n) 
      . (let vs = randbits n)  
      . .. (pi(b,v) . (newq q = basisv_of_bits b v) . qc!q ._0) (zip bs vs)
      . <continuation>

-- one line of code; no mechanism, other than an explicit statement of iteration (the `..` symbol), an anonymous nested process. Far simpler. So, how to make it work?

## Nested anonymous processes

Nested process definitions, which make use of values from the enclosing process, are nothing new in the pi calculus. Every process par uses them:

        <preamble>
        | process 1
        | process 2

Both process 1 and process 2 can call on names declared in the preamble. If we allowed anonymous process expressions, using &pi; just as anonymous function expressions use &lambda;, we could rewrite this as 

        <preamble>
        | (pi().process 1)()
        | (pi().process 2)()

-- we wouldn't gain anything by it, but it's not utterly outlandish.

## Logging with nested processes

The mechanism described so far (without the iteration proposal, which I shall return to) is already used in effect to provide logging subprocesses in qtpi. We can write a process

        proc P(params) = <process> with <logging>

where \<logging\> is a collection of numbered process bodies, for example (from BB84 QKD Alice)

      1: . log!bs . log!vs . _0
      2: . log!h0 . log!bs . log!h1 . log!bBs . _0 
      3: . log!rvs . _0
      4: . log!h2 . log!mask. log!h3 . log!checkbitsB . _0 
      5: . log![bool2bit q_check] . log![bool2bit c_check] . log![bool2bit enough] . _0
      7: . log!code . log!M . log!h4 . log!encryptedM . log!hks' . _0

and \<process\> can have insertions `/^<number>` to indicate that a particular logging process should be called at a particular point. From Alice, again

    (* tell each other the qbit bases we used - me first *)
    . (let h0 = hwc bs hks 0 w)
    . bsc!h0,bs                              (* send Bob my bases *)
    . bsc?(h1,bBs)                           (* receive his bases *)
    . /^2

The logging processes are restricted: they can't do any quantum steps; they can only send, not receive, on channels; they can only send classical values; they can't use process par or invocation. They are typechecked in line at each of their call sites -- i.e. they are nested processes and they might as well be anonymous, though they have numbers as names to allow them to be separated from the main process body. (And they can only be called once, because in effect they are inserted.)

## Resource-checking nested anonymous processes

In a parallel construct the arms of the par can't use the same quantum resource. But in calling a nested anonymous process

        <preamble>
        (new c)
        | (pi(params) . body . c!() . _0) (arguments)
        | c?(_) . <continuation>

 the body of the process is executed sequentially before the continuation. Should we resource-check it as such? I would say yes and no. Yes, \<body\>  could safely make access to free qbits (those defined in the preamble): that has no resource consequences for the continuation. We might even allow it to alter the lifetime of a free qbit -- send it in a message or measure it. But that couldn't be allowed if the call were iterated: then the second iteration wouldn't have access to that free qbit. So perhaps simpler to say that called processes can't measure or send free qbits. And also an argument to a called process can't be a free qbit, because that would allow two names for the same resource and oh dear oh dear oh dear. 
 
 So: free qbit access ok; free qbit measure or send not ok; free qbit as argument not ok.
 
 ### Parallel nested anonymous processes
 
 At the moment we don't have collections of qbits. Suppose that we did. Suppose that Q is such a collection. How about the following
 
        (new c)
        || (pi(i,q) . q-/-(b) . c!(i,b) ._0) Q
        
The `||` symbol is an explicit statement of parallelisation. This would create a number of parallel processes, each given one of the qbits in Q, each sending the result of measuring that qbit down channel `c` together with the index-position of that qbit in Q. This arises in the quantum election example, where Q would be a collection entangled in a W state. The process obeys the restrictions: no use of free qbits; no process invocations.

## Processes which return a result

The only way a process can return a message is to send a message. As, for example, in BB84 QKD Bob:

        . (new result) 
        | . ReceiveQBits([],qc,bsc,result)
        | . result?(bvs,message)
          . (let (bs,vs) = bvs)             (* bs, vs is what I saw *)
          . (let (h0, bAs) = message)       (* Alice's first classical message: bAs are her bases *)

        proc ReceiveQBits (bvs, qc, bsc, result) =
          + qc?(q)                   . 
                (let b = randbit ())
                q-/-[if b=0b1 then H else I](v) .
                ReceiveQBits((b,v)::bvs,qc,bsc,result)
          + bsc?(message)            . 
                result!(bvs,message) . 
                _0

The idea is that Bob should receive the qbits sent by Alice (either iteratively or recursively), without knowing how many bits there should be. This is accomplished by a recursive process `ReceiveQBits` which *either* receives a qbit, measures it in a randomly-chosen basis and records basis and result, then recurses, *or* receives Alice's first classical protocol message following the sequence of qbits.

Two things are happening here: one a sort of process fold across a sequence of inputs on channel qc; the other the notion of terminating a recursive or iterative fold across a stream of messages on one channel with a message on another channel. That second technique is surely too specific to incorporate into the language.

Things would be better if we could have a nested process: then, at least, the channels wouldn't have to be arguments. Then if we had `call` and `return` ... but that would perhaps be too much violence to the spirit of the pi calculus.

            <preamble, which declares qc and bsc>
          . (vproc ReceiveQBits(bvs) = + qc?(q) . (let b = randbit ())
                                                . q-/-[if b=0b1 then H else I](v) .
                                                . ReceiveQBits((b,v)::bvs)
                                       + bsc?(message) . _0 (rev bvs,message)
            )
          . (let (bvs, message) = ReceiveQBits([]))
          . (let (bs,vs) = bvs)             (* bs, vs is what I saw *)
          . (let (h0, bAs) = message)       (* Alice's first classical message: bAs are her bases *)

Maybe, maybe, maybe. A nested process like that would be resource-dodgy. Oh for recursive anonymous pi expressions ... (several bridges too far already).

