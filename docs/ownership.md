(I've deleted the html version of this file because git's rendering of this file is superior to an html browser's. So it's available at  

    https://github.com/mdxtoc/qtpi/blob/master/docs/ownership.md  
    
But if you are reading this then you already know that ...)

# Static treatment of ownership of qbits -- Resource-checking a program

I began to develop qtpi because of a remark of Guillaume Poly's. He'd noticed that a treatment of qbit-ownership transfer between processes was impossible in Microsoft's Q#, which was all about efficient simulation of quantum computation. But quantum protocols are mostly about passing quantum bits between processes, and hardly do any quantum computation.

A process calculus like CQP seemed like it might provide a solution to the ownership problem. Then I realised that the cloning problem is another side of the same coin, and therefore might also be treated at the same time.

The phrase *resource checking* harks back to my background in separation logic (I was there when ...). It was always something I wanted to do with heap programs, though I never knew how to do it accurately enough. (Others, of course, did better ...)

Qbits are the resource manipulated by quantum-protocol programs. Qtpi checks the correct use of those resources.

## Hubris
Oh, nemesis! I didn't read the Gay and Nagarajan paper properly (actually I wasn't given the right version to read). Much of this can be done with linear typing. And with the right language restrictions (see [the language description](https://github.com/mdxtoc/qtpi/blob/master/docs/qtpi_description.md/#restrictions)) almost all of it can. 

Although I think that many of the problems below can't happen any more within the language I've kept the implementation in case I decide to lift some or all of those restrictions.

## The ownership problem

Suppose *A* sends a qbit on a channel *c*

		A(c:^qbit) = (newq q) c!q. .. etc. A ..
	
and *B* receives it 

		B(c:^qbit) = c?(q1). .. etc. B ..
	
Suppose that we identify different named processes as happening on different machines in different places. Then surely in '*etc. A*', after it has sent the qbit elsewhere, *A* cannot do anything with *q*, like measure it, gate it or whatever. *B* in '*etc. B*', after it has received the qbit, clearly can play with *q1* exclusively: it **owns** it.

So it seems that it might be possible to use scoping to deal with ownership: in '*etc. A*', *q* could be treated as out of scope, whilst in '*etc. B*', *q1* is in scope. Bingo? You'd think so. And you'd be right, in a sense, with the right restrictions: it is possible to write a *linear type system* that can do the job. But in general you can't: it's **resourcing**, not scoping, a dynamic property of a value, not a not a static property of a name.

But process calculus is so restricted -- e.g. only tail recursion -- that it is possible to run a symbolic execution of all paths through a process definition to check that qbits are handled properly. (There is a potential problem in qtpi since it allows conditional expressions and applications of library functions, but see below.)

## The cloning problem

It is impossible to clone qbits. So a program should be incapable of making a copy of a qbit.

1. How about splitting into two processes?

			A() = (newq q) (B(q) | C(q))
	
			B(q1:qbit) = ...
	
			C(q2:qbit) = ..
	

	This has to be prohibited: *B* and *C* can't both exclusively inherit the same qbit.

2. How about going on as another process?

			A() = (newq q) B(q,q)
	
			B(q1:qbit, q2:qbit) = ...
	
	*B* doesn't own two separate qbits.
	
3. Values containing qbits as arguments?
	
			A() = (newq q) (let n = q,q) B(n)
			
			B(qt:qbit*qbit) = ...  
	
	Again, *B* doesn't own two separate qbits. 
	
3. How about sending the same qbit twice?

			A(c:^qbit*qbit) = (newq q) c!q,q . ...
		
			B(c:^qbit*qbit) = c?(q1,q2). ...
		
	*B* only owns one qbit, not two. 
	
4. How about a *let* binding?

			A() = (newq q) (let q'=q) ...
		
	*A* only creates one qbit to own. 
	
## Accounting problems

If we want to check ownership we have to account for the use of qbits. This throws up some obvious problems.
	
1. A conditional send?
	
			A(q1:qbit, q2:qbit, c:^qbit) = ... c!(if ... then q1 else q2 fi). ...
	
	Which qbit has been sent away, and which does *A* own after the send? 
	
2. Values containing qbits?

			(newq q) (let n = q,q) ...
			(newq q) (let qs = [q;q]) ... 
		
	In the first example a single qbit has three names: *q*, *fst n* and *snd n*. In the second we have three names as well: *q*, *hd qs* and *hd (tl qs)*. But in each case only one qbit. 
	
3. Conditional cloning?
	
			    a?(x) ... stuff using q1 and q2 ... 
			<+> b?(y) ... stuff using q2 and q3 ..
	
	This program uses *q1*, *q2* and *q3*, and there's no cloning issue because only one of the arms is executed. But then
	
			(a?(x) ... stuff using q1 and q2... 
			 <+> 
			 b?(y) ... stuff using q2 and q3 ..
			) 
			| 
			(if condition then ... stuff using q3 ... else ... stuff using q4 ... fi)
	
	There *might* be a cloning violation, or there might be good reason that the `b?(y)` arm of the guarded sum never actually executes when *condition* is true.
	
	(I don't suppose I can solve this problem. But an approach using continuations _might_ work.)
	
## Restrictions

Qbits are big fragile things. They are measured, sent through gates, transmitted through channels. If a program makes, for example, a tuple of qbits it is actually making a tuple of qbit *indices*, an index being the way that an implementation identifies the qbits it manipulates. 

It might seem reasonable to ban qbit-valued conditional and match expressions: they decrease the accuracy of resource-checking and can cause spurious cloning errors. A ban remains a possibility. Some uses are outlawed, such as

		c ! if a=0 then q1 else q2 fi

Others are harmless, such as

		if a=0 then q1 else q2 fi >> _H

Match expressions are equally problematic, but equally to be tolerated.

## A Resource-checking Algorithm

Qbits in existence when a process starts are delivered via its arguments. We assume (a non-cloning invariant) that distinct parameters name distinct bundles of resource. We name the qbits we can see in single qbit parameters, in tuples and in lists according to the path you must follow to get to them. 

When we read a qbit with *c*?(*q*) we know from the invariant that it is distinct from anything we own. So we give it a new name. It might be an old sent-away qbit coming back, but that's ok: treating it as new won't lead us astray.

Thus we can work out how names describe resource bundles. 'Let' bindings add to the fun, but don't create qbits. 'Newq' bindings do create named qbits, which we number. Reads add named qbits. Using a mapping from names to resource (an 'environment') we can calculate what resource an expression uses. We check that process Pars (*P*|*P*|...|*P*), process calls *N*(*E*,*E*,...,*E*) and writes *c*!*E*,*E*,...,*E* use disjoint resources in their components, preserving the non-cloning invariant. And in the latter two cases, any lists or tuples built to make the *E*s have to have disjoint parts as well.

To handle the ownership problem, a symbolic execution -- i.e. an abstract interpretation, I believe -- keeps track, in a qbit-name-indexed 'state', of which qbits are sent away in writes.  If an expression uses a sent-away qbit then it's a resourcing error. 

And that's it: one pass through a process definition gives us a comprehensive check on ownership and cloning.

## Hubris, Nemesis again?

No free lunch has arrived. A symbolic execution is not a perfect solution. But it appears to be sound -- if it says a program is ok, it is ok. On the other hand it is evidently incomplete -- there are valid programs to which it will object.

Inaccuracies arise with conditional expressions and guarded sums. Conditional expressions have been noted already: they are assessed as using the resources of both arms, though an execution uses only one arm at a time. They may not be a problem in principle, since every program using a qbit-valued conditional expression could be rewritten to use a conditional process.

There remains a problem. The resources used by a conditional process are assessed as the union of the resources used by each of its arms. The resources used by a guarded sum are assessed as the union of the resources of all its arms. Then a parallel composition *P*|*P*|...|*P* of guarded sums and/or conditional processes may cause more cloning objections than an actual execution could actually exploit. But this will be over-caution: incompleteness, not unsoundness.

Quantum protocols are perhaps computationally rather simple. I have hope that a simple treatment will be useful, even though it sometimes complains when it shouldn't, provided it is always right when it approves.

## Functions and qbits: more nemesis

Late on in the game, I realised that the resource-checking algorithm doesn't deal properly with functions. A function definition which has  non-classical free variables provides access, when it's applied, to those free variables. So a function sent in a message could provide access from the receiving process to a qbit in the sender's space. Within a single process a function could provide access to a sent-away qbit or attempt access to an already-measured qbit.

Partially-applied functions complicate things too: *f q*, where *f* has more than one parameter, bakes in access to *q* even if *f*'s definition has no non-classical free variables.

Perhaps this could be dealt with, but none of the schemes I have considered seem to work. So I have reluctantly concluded that it is best to apply a very severe language restriction: no non-classical free variables, and no non-classical parameters. See [the language restrictions](https://github.com/mdxtoc/qtpi/blob/master/docs/qtpi_description.md/#restrictions) for details.


  