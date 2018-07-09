# Static treatment of ownership of qbits

## The dream

Suppose *A* sends a qbit on a channel *c*

    A(c:^qbit) = (newq q) c!q . .. more A ..
    
and *B* receives it on the same channel

    B(c:^qbit) = c?(q'). .. more B ..
    
Suppose that we identify different named processes as happening on different machines in different places. Then surely in *more A*, *A* cannot do anything with *q*, like measure it, gate it or whatever. *B* in *more B* clearly can play with *q'* exclusively: it **owns** it.

So it seems that it might be possible to use scoping to deal with ownership: in *more A*, *q* could be out of scope, whilst in *more B*, *q'* is in scope. Bingo?

## Problems

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
    
## Resources

Clearly a qbit is a resource. It's indivisible and can't be duplicated. So the kind of casual duplication of tupling *q,q* or listing *q::q::qs* or any of the four problems above has to be outlawed.

If we required that tuple elements didn't overlap in terms of resource, and that qbit names bind unique qbits, we might be out of the woods. Qbit lists, and lists of any type involving a qbit, probably have to be outlawed.

Then we can do the scope thing.

That's my plan anyway.
  