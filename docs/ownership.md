# Static treatment of ownership of qbits -- Resource-checking a program

My original inspiration was the ownership problem, triggered by a remark of Guillaume Poly's. He'd noticed that a treatment of qbit-ownership transfer between processes was impossible in Microsoft's Q#, which was all about efficient simulation of quantum computation. But quantum protocols are mostly about passing quantum bits between processes, and hardly do any quantum computation.

A process calculus like CQP seemed like it might provide a solution to the ownership problem. Then I realised that the cloning problem is another side of the same coin, and therefore might also be treated at the same time.

The phrase *resource checking* harks back to my background in separation logic (I was there when ...). It was always something I wanted to do with heap programs, though I never knew how to do it accurately enough. (Others, of course, ...)

Qbits are the resource manipulated by quantum-protocol programs. Qtpi checks the correct use of those resources.

## The ownership problem

Suppose *A* sends a qbit on a channel *c*

		A(c:^qbit) = (newq q) c!q. .. etc. A ..
	
and *B* receives it 

		B(c:^qbit) = c?(q1). .. etc. B ..
	
Suppose that we identify different named processes as happening on different machines in different places. Then surely in '*etc. A*', after it has sent the qbit elsewhere, *A* cannot do anything with *q*, like measure it, gate it or whatever. *B* in '*etc. B*', after it has received the qbit, clearly can play with *q1* exclusively: it **owns** it.

So it seems that it might be possible to use scoping to deal with ownership: in '*etc. A*', *q* could be treated as out of scope, whilst in '*etc. B*', *q1* is in scope. Bingo? You'd think so. Actually not: it's **resourcing**, not scoping, a dynamic property of a value, not a not a static property of a name.

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
	
	(I 'solve' this problem by prohibiting it: see below.)
	
2. Values containing qbits?

			(newq q) (let n = q,q) ...
			(newq q) (let qs = [q;q]) ... 
		
	In the first example a single qbit has three names: *q*, *fst n* and *snd n*. In the second we have three names as well: *q*, *hd qs* and *hd (tl qs)*. But in each case only one qbit.
	
	(This problem can be handled: see below.)
	
3. Conditional cloning?
	
			a?(x) ... stuff using q1 and q2 ... 
			+ 
			b?(y) ... stuff using q2 and q3 ..
	
	This program uses *q1*, *q2* and *q3*, and there's no cloning issue because only one of the arms is executed. But then
	
			(a?(x) ... stuff using q1 and q2... 
			 + 
			 b?(y) ... stuff using q2 and q3 ..
			) 
			| 
			(if condition then ... stuff using q3 ... else ... stuff using q4 ... fi)
	
	There *might* be a cloning violation, or there might be good reason that the `b?(y)` arm of the guarded sum never actually executes when *condition* is true.
	
	(I don't suppose I can solve this problem. My algorithm will object to this program.)
	
## Restrictions

Qbits are big fragile things. They are measured, sent through gates, transmitted through channels. If a program makes, for example, a tuple of qbits it is actually making a tuple of qbit *indices*, an index being the way that an implementation identifies the qbits it manipulates. 

  * **No comparison of qbits, or values containing qbits**
	
	Qbits aren't things you can compare. But you could compare indices ... 
	
	A qbit's index is private information for the implementation. In Qtpi it's currently a global integer. So if you ask whether two qbits are the same -- e.g.
  
			if q1=q2 then ..
		
	you either asking for something impossible (compare the actual qbits) or doing something naughty (exploiting the implementation of the language). Not allowed, either way. It just feels wrong.

  * **A channel is either `^qbit` or `^classical`**
    
	Protocol descriptions talk of processes sending qbits to each other and separately communicating information like basis and value over classical channels. So I require that a channel either carries single qbits, or it carries values which don't include qbits. Easy to check.
	
  * **Function applications can't deliver qbits, or values containing qbits**
	
	You and I know what we mean by *hd* and *tl*, by *fst* and *snd*. But these are library functions: the interpreter doesn't understand them. Even though it knows from type information that given  *qs: qbit list*, *hd qs* will deliver a qbit, it doesn't know which one of the list it will get. And even we don't know much about *hd (rev qs)*.
	
	Pattern matching softens the blow of this restriction, allowing the program to take apart lists and tuples containing qbits. 
		
The first two restrictions make the resource-checking algorithm simpler. The third is essential.I haven't imposed a restriction which entirely prevents tuples and lists containing qbits since it appears to be unnecessary and would be very restrictive.

It might seem reasonable to ban qbit-valued conditional and match expressions: they decrease the accuracy of resource-checking and can cause spurious cloning errors. A ban remains a possibility. Some uses are outlawed, such as

		c ! if a=0 then q1 else q2 fi

Others are harmless, such as

		if a=0 then q1 else q2 fi >> _H

Match expressions are equally problematic, but equally to be tolerated.

## A Resource-checking Algorithm

Qbits in existence when a process starts can be delivered via its arguments. We assume (a non-cloning invariant) that distinct parameters name distinct bundles of resource. We number the qbits we can see in single qbit parameters or in tuples. We don't do much with lists of qbits, but we number them when they appear in match patterns.

When we read a qbit with *c*?(*q*) we know from the invariant that it is distinct from anything we own. So we give it a new number. It might be an old sent-away qbit coming back, but that's ok: treating it as new won't lead us astray.

Thus we can work out how names describe resource bundles. 'Let' bindings add to the fun, but don't create qbits. 'Newq' bindings do create named qbits, which we number. Reads add named qbits. Using a mapping from names to resource (an 'environment') we can calculate what resource an expression uses. We check that process Pars (*P*|*P*|...|*P*), process calls *N*(*E*,*E*,...,*E*) and writes *c*!*E*,*E*,...,*E* use disjoint resources in their components, preserving the non-cloning invariant. And in the latter two cases, any lists or tuples built to make the *E*s have to have disjoint parts as well.

To handle the ownership problem, a symbolic execution -- i.e. an abstract interpretation, I believe -- keeps track, in a qbit-name-indexed 'state', of which qbits are sent away in writes.  If an expression uses a sent-away qbit then it's a resourcing error. 

And that's it: one pass through a process definition gives us a comprehensive check on ownership and cloning.

When process definitions start to use parameterised types like *'a list*, we shall have to check their instantiations rather than their definitions. But that is for the future. It won't be a problem: we only have to make at most one process-check per call of a process.

## Hubris, Nemesis?

No free lunch has arrived. A symbolic execution is not a perfect solution. But it appears to be sound -- if it says a program is ok, it is ok. On the other hand it is evidently incomplete -- there are valid programs to which it will object.

Inaccuracies arise with conditional expressions and guarded sums. Conditional expressions have been noted already: they are assessed as using the resources of both arms, though an execution uses only one arm at a time. They may not be a problem in principle, since every program using a qbit-valued conditional expression could be rewritten to use a conditional process.

There remains a problem. The resources used by a conditional process are assessed as the union of the resources used by each of its arms. The resources used by a guarded sum are assessed as the union of the resources of all its arms. Then a Process par (*P*|*P*|...|*P*) of guarded sums and/or conditional processes may seem cause more cloning objections than an actual execution could actually exploit. But this will be over-caution: incompleteness, not unsoundness.

There may be new problems when I allow pattern-matching and encounter programs that use lists of qbits (which some protocols may need). There will certainly be complications, but I doubt there will be novel incompleteness.

Quantum protocols are perhaps computationally rather simple. I have hope that a simple treatment will be useful, even though it sometimes complains when it shouldn't, provided it is always right when it approves.

  