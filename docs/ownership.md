# Static treatment of ownership of qbits -- resourcing

## The first problem

Suppose *A* sends a qbit on a channel *c*

	A(c:^qbit) = (newq q) c!q . .. etc. A ..
	
and *B* receives it on the same channel

	B(c:^qbit) = c?(q'). .. etc. B ..
	
Suppose that we identify different named processes as happening on different machines in different places. Then surely in *etc. A*, after it has sent the qbit elsewhere, *A* cannot do anything with *q*, like measure it, gate it or whatever. *B* in *etc. B*, after it has received the qbit, clearly can play with *q'* exclusively: it **owns** it.

So it seems that it might be possible to use scoping to deal with ownership: in *etc. A*, *q* could be out of scope, whilst in *etc. B*, *q'* is in scope. Bingo? You'd think so. Actually it's __resourcing__, not scoping: a dynamic not a static property of a value.

But process calculus is so restricted -- e.g. only tail recursion -- that it is possible to run a symbolic execution of all paths through a process definition to check that qbits are handled properly

## More problems

1. How about splitting into two processes?

		A() = (newq q) (A'(q) | A''(q))
	
		A'(q1:qbit) = ...
	
		A''(q2:qbit) = ..
	

	*A'* and *A''* can't both exclusively inherit the same qbit.

2. How about going on as another process?

		A() = (newq q) A'(q,q)
	
		A'(q1:qbit, q2:qbit) = ...
	
	*A'* doesn't own two separate qbits.
	
3. How about sending the same qbit twice?

		A(c:^qbit*qbit) = (newq q) c!q,q . ...
		
		B(c:^qbit*qbit) = c?(q1,q2). ...
		
	*B* only owns one qbit, not two.
	
4. How about a *let* binding?

		A() = (newq q) (let q'=q) ...
		
	*A* only creates one qbit to own.
	
5. How about a conditional send?
	
		A(q1:qbit, q2:qbit, c:^qbit) = ... c!(if ... then q1 else q2 fi)
	
	Which qbit does *A* own?
	
6. Values containing qbits?

		(newq q) (let n = q,q) ...
		(newq q) (let qs = [q;q]) ... 
		
	In the first example a single qbit has three names: *q*, *fst n* and *snd n*. In the second we have three names as well: *q*, *hd qs* and *hd (tl qs)*. But in each case only one qbit.
	
## Restrictions

Qbits are big fragile things. They are measured, sent through gates, transmitted through channels. If we make, for example, a tuple of qbits we are actually making a tuple of qbit *indices*, an index being the way that a process identifies the qbits it manipulates. 

  * **No comparison of qbits, or values containing qbits**
	
	The qbit index is private information for the implementation. In Qtpi it's currently a global integer. So if you ask whether two qbits are the same -- e.g.
  
			if q1=q2 then ..
		
	you are messing with the implementation of the interpreter. Not allowed.

  * **A channel is either `^qbit` or `^classical`**
    
	Protocol descriptions talk of processes sending qbits to each other and separately communicating information like basis and value over classical channels. So a channel either carries single qbits, or it carries values which don't include qbits. Easy to check after type assignment (typechecking).
	
  * **Function applications can't deliver qbits, or values containing qbits**
	
	You and I think we know what we mean by *hd* and *tl*, by *fst* and *snd*. But these are library functions: the interpreter doesn't understand them. So though we know from its type that given  *qs: qbit list*, *hd qs* will deliver a qbit, we don't know which one of the list it will give us. And we certainly don't know what *hd (rev qs)* does.
	
	In the (possibly near) future it will be possible to take tuples and lists apart using pattern-matching, which the interpreter does understand.

The first two restrictions make the resourcing algorithm simpler. The third is essential.

## A Resourcing algorithm

Qbits in existence when a process starts can be delivered via its arguments. We assume (our invariant) that distinct parameters name distinct bundles of resource. We number the qbits we can see in single qbit parameters or in tuples. We don't do much with lists of qbits, but since you can't take them apart yet (see above) that's not yet a problem.

When we read a qbit *c*?(*q*) we know from the invariant that it is distinct from anything we own. So we give it a new number. It might be an old sent-away qbit coming back, but that's ok: treating it as new won't lead us astray.

So we can work out which names name what resource bundles. 'Let' bindings add to the fun, but don't create qbits. 'Newq' bindings do create qbits, which we number. Then we can calculate what resource an expression uses. Therefore we can check that process Pars (*P*|*P*|...|*P*), process calls *N*(*E*,*E*,...,*E*) and writes *c*!*E*,*E*,...,*E* use disjoint resources in their components -- preserving the invariant.

Our symbolic execution keeps track, in a symbolic 'state', of which qbits are sent away in writes. If an expression uses a sent-away qbit then it's a resourcing error.

And that's it: one pass through a process definition gives us a comprehensive check.

When process definitions start to use parameterised types like *'a list*, we shall have to check their instantiations rather than their definitions. But that is for the future.
  