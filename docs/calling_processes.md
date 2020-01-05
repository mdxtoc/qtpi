# Embedded processes

The pi calculus is a stark language, invented to explore the semantics of processes. Qtpi uses the pi calculus, augmented with qbit creation and quantum steps. It's also augmented with `let` declarations and `match` conditionals. Qtpi is intended as a programming language, and it's reasonable to include mechanisms designed to increase clarity, even at the expense of starkness.

On the other hand, qtpi exploits the starkness of the pi calculus to enable it to make a static check on ownership and uniqueness of qbits, so as to prohibit sharing between processes and cloning. Additions can't be allowed to compromise that check.

It would be useful to allow subprocesses to be defined within the body of an enclosing process, so that they can use names free at the point of definition. This mechanism has already allowed qtpi to have *logging* subprocesses, so that a computation's description isn't obscured by commands which log process state, progress etc. It will shortly allow iterated processes as well.

If embedded processes can be compiled into the pi calculus, then we can understand how to check their resource use statically and we can safely include them in the language.

## Calling a non-embedded process
 
A pi calculus process body is more or less a straight-line sequence of steps; guarded sums allow us to choose between sequences; conditionals (and matches in qtpi) likewise allow choice. But there's no looping, and a process terminates (`_0` in qtpi) or changes into another process by a process invocation. That invocation, unlike a conventional function call, never returns. But, given some restrictions on the shape of a process body, we can imitate call and return using process-par and messages.

Suppose process `P` has a body which always terminates with `_0`, not with a process invocation, and doesn't contain a process-par. Suppose we make a new process `P`<sub>`r`</sub> by replacing each `_0` by `rc!()._0`, where `rc` isn't used elsewhere in `P`, and adding `rc` to the parameters. Then the construct

        <preamble>
        (new rc)
        | Pr(arguments,rc)
        | rc?(_) . <continuation>

will execute the preamble, then the body of `P`, and finally the continuation. In effect `P` is called, and returns.

Since this is just a bit of programming within the pi calculus tradition, normal qtpi resource-checking can be applied: the two apparently-parallel (but really sequential) arms can't share any quantum resource. But if `P` were to take a qbit as argument, then the call takes that qbit out of the ownership of the calling process, and it can't be used in the continuation. 

We could use this pattern as the compiled program which corresponds to `<preamble> . call P(arguments) . <continuation>`, if it were helpful to have such a construct in qtpi's language. (**NB**: I'm not proposing to include `call` in qtpi: it's a device to aid discussion of simulation and compilation.)

Note that the mechanism requires that the called process `P` can't end with a process invocation (unless it's a recursive invocation of `P`) and can't use a process-par, else we couldn't insert the `rc!()` steps which signal its termination to the calling process.

### Returning a value

There's no reason why the return channel `rc` could not carry a return value, in which case `P`<sub>`r`</sub> could return a value. 

## Recursive non-embedded-process call

If `P` is recursive then some of its executions will invoke a new execution of itself. Change those to calls of `P`<sub>`r`</sub> and we can call recursive `P`<sub>`r`</sub> and the same mechanism works: `P`<sub>`r`</sub> is called, and it returns. I used this mechanism to simulate BB84 QKD. Alice defines a list of bases `bs` and values `vs` and sends qbits to Bob encoding those values down the previously-defined channel `qc`. (Please ignore the flagrant use of extra unnecessary separating dots in qtpi code: I'm experimenting with it to make programs easier to write and to read -- but note that otherwise this is just standard qtpi stuff, with no fancy constructs)

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

For each `(b,v)` pair, `SendQbits` makes a new qbit `q` and sends it down channel qc. But lots of mechanism intruding on what ought to be a simple iterative mechanism: send one qbit for each (*b*,*v*) pair. For solution see [Iterative embedded-process call](#iterativeembeddedprocesscall).

## Defining and calling an embedded process

Non-embedded processes don't have free names, other than the names of other processes that they might invoke, and it would seem that if we are to call process `P` it would be better if it didn't invoke other processes. Embedded processes do have free names -- that's the point.

Suppose that we have a program

          <preamble>
        . (proc R(x,y,z) = <process body>)
        . <intermediate>
        . call R(argA,argB,argC)
        . <continuation>
        
-- a process `R` defined so that it can make use of names from `<preamble>` and with arguments `x`, `y` and `z`, called at a later point in the process. (Again **nb**: I'm not proposing a `call` mechanism, just using it to facilitate description.)

It is possible, I believe, to implement such a mechanism in pure pi calculus, using process arguments to deal with free names in `<process body>` and messages to deal with arguments in the `call`. But I do not propose that, so I don't describe it. Instead I propose (and have already implemented) **process closures**: processes with environments. And I also propose (and have already implemented) a `proc` declaration, though for the time being only implemented as an interpretation mechanism and not given a syntactic form.

Given `proc`, the `call` mechanism could be just as for non-embedded processes -- i.e. construct `R`<sub>`r`</sub> using a fresh channel `rc` and call that. But as a language mechanism it would all get a bit strange, so I don't actually propose it.

<a name="iterativeembeddedprocesscall"></a>
## Iterative embedded-process call

The `call` encoding of `SendQbits` works perfectly as an execution mechanism. But it doesn't work well as a description, because it's mostly mechanism. The `sent` channel, the argument `qc`, the `match` construct: all of it is mechanism to describe a simple process iteration. Ten lines of code in total, only two of them about what's really happening.

Here's what I would prefer to write, and intend to implement:

        <preamble>
      . (let bs = randbits n) 
      . (let vs = randbits n)  
      . .* (b,v)  ((newq q = basisv_of_bits b v) . qc!q ._0) (zip bs vs)
      . <continuation>

This is an expression of process iteration, giving the process arguments, the process body, the list to be iterated over. For each (*b*,*v*) in (*zip* *bs* *vs*), make a new qbit *q* and send it down channel *qc*, and that's all
-- one line of code; no mechanism, other than an explicit statement of iteration (the `.*` symbol), an anonymous nested process, and a statement of the list of values to be used. Far simpler. So, how to make it work?

### Embedded anonymous processes

Embedded process definitions, which make use of values from the enclosing process, are nothing new in the pi calculus. Every process par uses them:

        <preamble>
        | process 1
        | process 2

Both process 1 and process 2 can call on names declared in the preamble. If we allowed anonymous process expressions, using &tau; just as anonymous function expressions use &lambda;, we could rewrite this as 

        <preamble>
        | (tau().process 1)()
        | (tau().process 2)()

-- we wouldn't gain anything by it, but it's not utterly outlandish.

### Logging with embedded processes

The mechanism described so far (without the iteration proposal, which I shall return to) is already used in effect to provide logging subprocesses in qtpi. We can write a process

        proc P(params) = <process> with <logging>

where \<logging\> is a collection of numbered process bodies, for example (from BB84 QKD Alice)

      1: . log!bs . log!vs . _0
      2: . log!h0 . log!bs . log!h1 . log!bBs . _0 
      3: . log!rvs . _0
      4: . log!h2 . log!mask. log!h3 . log!checkbitsB . _0 
      5: . log![bool2bit q_check] . log![bool2bit c_check] . log![bool2bit enough] . _0
      7: . log!code . log!M . log!h4 . log!encryptedM . log!hks' . _0

and `<process>` can have insertions `/^<number>` to indicate that a particular logging process should be called at a particular point. From Alice, again

    (* tell each other the qbit bases we used - me first *)
    . (let h0 = hwc bs hks 0 w)
    . bsc!h0,bs                              (* send Bob my bases *)
    . bsc?(h1,bBs)                           (* receive his bases *)
    . /^2
      <etc>

The logging processes are restricted: they can't do any quantum steps; they can only send, not receive, on channels; they can only send classical values; they can't use process par or process invocation. They are typechecked in line at their call sites -- i.e. they are embedded processes and they might as well be anonymous, though they have numbers as names to allow them to be separated from the main process body. And they can only be called once, because in effect they are inserted.

The code produced for `/^2` in the Alice example above is

          (new #chan#2)
        . (proc #mon#Alice#2 = tau () . log!h0 . log!bs . log!h1 . log!bBs . #chan#2!() . _0)
        | #mon#Alice#2 ()
        | #chan#2!() . <etc>

-- define a fresh channel (use of `#` guarantees it); define a fresh embedded process which signals completion on that channel; '`call`' that process. (I could get away without the `proc` declaration, but for tracing purposes I like to give the logging process a name.)

### Iteration with embedded processes (a proposal)

Suppose we have a process `Iter#`

       proc Iter# (xs,P,rc) =
         match xs .
          + []    . rc!() . _0
          + x::xs . (new callc)
                    | P(x,callc)
                    | callc?(_) . Iter#(xs,P,rc)

then we might compile

        . .* (b,v)  ((newq q = basisv_of_bits b v) . qc!q ._0) (zip bs vs)
        . <continuation>

-- the iterative SendQbits example above -- into

          (new iterc#)
        . (proc iterp# = tau (x#,rc) . (let (b,v) = x#) 
                                       (newq q = basisv_of_bits b v) 
                                       . qc!q 
                                       . rc!() 
                                       . _0
          )
        | Iter# (zip bs vs, iterp#, iterc#)
        | iterc#(_) . <continuation>

A solution, I think.

## Resource-checking embedded processes

In a parallel construct the arms of the par can't use the same quantum resource. But in calling a nested anonymous process

        <preamble>
        (new rc)
        | (tau(params) . <body> . rc!() . _0) (arguments)
        | rc?(_) . <continuation>

 `<body>` is executed sequentially before `<continuation>`. Should we resource-check it as such? I would say yes and no. Yes, `<body>`  could safely make access to free qbits (those defined in the preamble): that has no resource consequences for the continuation. We might even allow it to alter the lifetime of a free qbit -- send it in a message or measure it. But that couldn't be allowed if the call were iterated: then the second iteration wouldn't have access to that free qbit. So perhaps simpler to say that called processes can't measure or send free qbits. And also an argument to a called process can't be a free qbit, because that would allow two names for the same resource and oh dear oh dear oh dear. 
 
 So: free qbit access ok; free qbit measure or send not ok; free qbit as argument not ok.
 
 ### Parallel nested anonymous processes
 
 At the moment we don't have collections of qbits. Suppose that we did. Suppose that Q is such a collection. How about the following
 
        (new rc)
        . |* (i,q) (q-/-(b) . rc!(i,b) ._0) Q
        
The `|*` symbol is an explicit statement of parallelisation. This would create a number of parallel processes, each given one of the qbits in Q, each sending the result of measuring that qbit down channel `rc` together with the index-position of that qbit in Q. This arises in the quantum election example, where Q would be a collection entangled in a W state. The process obeys the restrictions: no use of free qbits; no process invocations.

## Processes which return a result (again)

The only way a process can return a result is to send a message just before termination. As, for example, in BB84 QKD Bob:

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

The idea is that Bob should receive the qbits sent by Alice (either iteratively or recursively), without knowing how many bits there should be. This is accomplished by a recursive process `ReceiveQBits` which *either* receives a qbit, measures it in a randomly-chosen basis and records basis and result, then recurses, *or* receives Alice's first classical protocol message following the sequence of qbits. (**NB**: this is nice programming, but is it nice in reality: can one imagine a receiver which looks for qbits until it receives a classical message? I think I can imagine that, but I don't think I could imagine a receiver which looks for qbits on one channel until it receives a qbit on another. Or can I?)

Two things are happening here: one a sort of process fold across a sequence of inputs on channel qc; the other the notion of terminating a fold across a stream of messages on one channel with a message on another channel. That second technique is surely too specific to incorporate into the language.

Things would be better if we could have a nested process: then, at least, the channels wouldn't have to be arguments. Then if we had `call` and `return` ... but that would perhaps be too much violence to the spirit of the pi calculus.

            <preamble, which declares qc and bsc>
          . (proc ReceiveQBits(bvs) = + qc?(q) . (let b = randbit ())
                                               . q-/-[if b=0b1 then H else I](v) .
                                               . ReceiveQBits((b,v)::bvs)
                                      + bsc?(message) . _0 (rev bvs,message)
            )
          . (let (bvs, message) = ReceiveQBits([]))
          . (let (bs,vs) = bvs)             (* bs, vs is what I saw *)
          . (let (h0, bAs) = message)       (* Alice's first classical message: bAs are her bases *)

Maybe, maybe, maybe. An embedded process like that would be resource-dodgy. Oh for recursive anonymous `tau` expressions ... (several bridges too far already: this is getting silly).

