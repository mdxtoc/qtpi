(I used to distribute an html version of this file. But git's rendering is better than a browser's, so now it's exclusively at

        github.com/mdxtoc/qtpi/blob/master/docs/qtpi_description.md

But if you are reading it you know that already ...)

# qtpi language description

Qtpi is based on CQP (Gay & Nagarajan, POPL 2005) and therefore on the pi calculus. Some changes are cosmetic (e.g. fewer square brackets, fewer capital letters); some for convenience (no mandatory types, because there's a typechecker); some because quantum-state-changing operations (applying gates, measurement) should be protocol steps; and some are just cosmetic.

The expression language is moving closer to Miranda: '`where`' clauses, offside parsing and, eventually, laziness. The process language is beginning to exploit the offside parser.

## The offside rule

Most languages use lots of brackets in their syntax. You often have to use brackets in OCaml, for example, around the stuff after `then`, because the `else` part can be missing (i.e. no closing bracket for `then`) and likewise after the `else` because there's no closing `fi`.

When I began to implement Qtpi I thought that I'd do the Algol 68 thing and include `fi`. When I realised I needed pattern matching, I introduced a construct which started `match` and ended `hctam`. It looked horrible.

Landin's *offside rule* makes closing brackets unnecessary. In the Miranda expression *E* `where` *E'*, *E'* mustn't be left of `where`, and can't be left of its own first token. This disambiguates things like 

		hwc key message
		  where message = packets [] bits
		                    where bits = f message
		                    where f = g k
		  where key = ...
	
-- the first and fourth `where`s attach to hwc key message; the second and third attach to packets [] bits.

So far the offside parser applies to function definitions (expression to the right of '='), to `where` clauses, to `match`es in processes and expressions, to guarded sums, and to parallel process compositions.

## Grammar 

Processes *P*, input-output steps *IO*, quantum steps *Q*, expressions *E*, types *T*, process names *N*, variable names *x*, parameters *par*, patterns *pat*, gate expressions *G*. Square brackets surround optional elements.

* Program description

	A program is a sequence of process and function definitions. One of the process descriptions must be `System`, which must have no parameters.

  | `proc` *N* `(`  *par*  `,`  ... `,` *par* `)` = *P*  
  | `fun` *x* *pat* ... *pat*  = *E*  
  | `fun` *x* *pat* ... *pat* `:` *T* = *E*  
  
  * Types are optional in process parameters, as everywhere.
  * As with `let` and with reads `E?(pat)`, function parameters are bullet-proof: underscore `_`, names and unit, but otherwise no constants and definitely no lists.
  * Function parameters may include a type, and the result type of the function may be given. This allows you to define functions with types like `bit list -> 'a list -> 'a list`.
  * The arguments and result of a function must be entirely classical -- i.e. have nothing to do with qbits.
  * To allow mutually-recursive definitions, one `fun` can be followed with several definitions.
  
* Process *P* 

  | *Q* `.` *P*  
  | `+` *IO* `.` *P* ... `+` *IO* `.` *P*   
  | `|` *P* ... `|` *P*   
  | `if` *E* `then` *P* `else` *P* `fi`  
  | `match` *E* `.` `+` *pat* `.` *P* ... `+` *pat* `.` *P*   
  | `( new` *par*  `,`  ... `,` *par* `)` *P*   
  | `( newq` *par* [ `=` *E* ] `,`  ... `,` *par* [ `=` *E* ] `)` *P*  
  | `( let` *pat* `=` *E* `)` *P*  
  | *N* `(` *E*  `,`  ... `,` *E*  `)`  
  | `(` *P* `)`  
  | `_0`

  * A guarded sum starts with a `+`, and a parallel composition starts with a `|`. Neither needs to be bracketed, because the offside parser ensures that everything is to the right of the `+` or `|`, as appropriate.  
  * matches also use the `+` separator, and the offside parser.  
  * `new` creates channels, as in the pi calculus &nu;.    
  * `newq` creates qbits. Initialisation to basis vectors is optional (without it you get (*a<sub>i</sub>*`|0>`+*b<sub>i</sub>*`|1>`), for unknown *a<sub>i</sub>* and *b<sub>i</sub>*, where *a<sub>i</sub>*<sup>2</sup>+*b<sub>i</sub>*<sup>2</sup>=1).  
  * `let` expressions use a restricted form of pattern -- no constants, no lists -- so they can't fail to match.  
  * `_0` is the null process (i.e. termination). I would have used `()` (null parallel or null guarded sum: same difference) but it would have caused parsing problems.  
  * `{` *E* `}` `.` *P* is no longer included. It was used exclusively for printing, and the output channels out and outq now do the job.  
  * You can execute an arbitrary expression via a 'let' binding, if you wish.  Very non-pi if you write `(let _ =` *E*`)`. 
  
* Quantum step *Q*
  
  | *E* `,` *E* `,` ... `,` *E* `>>` *G*    
  | *E* `=?` (*pat*)    
  | *E* `=?` `[` *E* `;` ... `;` *E* `]` (*pat*)    

  * '`>>`' is 'send through a gate'; each left-hand *E* must describe a single qbit. The arity of the input tuple must match the arity of the gate (e.g. _H takes one qbit, _Cnot takes 2, _Fredkin if we had it would take 3, and so on).  
  * `=?` is measure, in the computational basis defined by `|0>` and `|1>`.  The parameter *par* binds the single-bit result. 
  * Measurement takes a pattern, either `_` or *x*. As you'd expect, if the pattern is a name then the result of the measurement (a bit 0b0 or 0b1) is bound to the name *and the qbit vanishes* (is used up). If it's `_` then the result of the measurement is ignored, but the qbit remains, transformed to `|0>` or `|1>`. That is, qbits are destroyed on *detection*, not on measurement (as in experiments with polaroid plastic film).
  * The optional square-bracketed *E* list is a gate expression controlling the measurement basis: for example `[_H]` specifies measurement in the Hadamard basis, and `[_I]` the computational basis. If there's more than one gate it specifies measurement in the basis defined by the matrix product of those gates. Internally `q=?[G](b)` is equivalent to `q>>G . q=?(b) . q>>G*` where `G*` is the conjugate transpose of `G`. (Somewhat more complicated if *q* is part of an entanglement: for a two-bit entanglement we must use `G><G` and `(G><)*` where `><` is tensor product; and so on for larger entanglements.) 
  * CQP had `*=` for measure, which looked like an assignment, so (at Guillaume Poly's suggestion) I changed it to `=?`.   

* Input-output step *IO*  

  | *E* `?` `(` *pat* `)`    
  | *E* `?` `_`    
  | *E* `!` *E*    

  * '`?`' is receive, as in many implementations of the pi calculus: *E* is a channel; the pattern is bracketed, as is the name in the pi calculus. The pattern is restricted as in a `let`  binding -- underscore allowed, no constants except `()`, no lists.   
  * '`!`' is send, as in many implementations of the pi calculus: the first *E* is a channel; the output expression can of course be an unbracketed tuple. (Miranda style says tuples must be bracketed: not this one.)  
  * Channels each carry either a qbit or a classical value (one not including any qbits). 
  * Channels can be buffered. The level of buffering is controlled with the `-chanbuf_limit` switch. (The default is no buffering - i.e. synchronised message-passing -- because I think it makes most sense with guarded commands).
  
* Parameter *par*

  | *x*  
  | *x* `:` *T* 
  
  * Parameter type specs are optional, always.
  
  
* Type *T* 

  | `qbit`  
  | `unit`  
  | `num`  
  | `bool`  
  | `bit`  
  | `string`  
  | `char`  
  | `basisv`  
  | `qstate`  
  | `'`*x*  
  | `''`*x*  
  | *T* `list`  
  | *T* `*` ... `*` *T*  
  | `^` *T*  
  | *T* `->` ... `->` *T*  
  | *T* `process`  
  | `(` *T* `)`  

  * These types are still ML style. Miranda style is neater (`[num]` rather than `num list`, `(num,bit)` rather than `num*bit`, and they don't need syntactic precedence). One day soon ... 
  *  '*num*' is the type of numbers: unbounded integers and unbounded-precision rationals (fractions). So that we can do proper arithmetic. Using *num* rather than *int* can cause some problems: some library functions, such as *take* and *drop*, really don't work with fractional arguments (or, at least, I can't decide what they do), and you may have to make use of *floor*.
  * Range types were in original CQP, but are no longer in qtpi. They are hard to deal with in the typechecker and are currently pretty useless, but if I can make a subtyping typechecker they may come back (I do hope so).  
  * '*bit*' ought to be a subtype of *int*, but I can't force the typechecker to agree.
  * `basisv` is the type of basis vectors (see below).  
  * `qstate` is the type of the result of the *qval* function (see below). It's a peek at the simulator state. But qstates can't be compared or manipulated in any way. The only useful thing you can do with a *qstate* is to send it down the outq output channel, which prints it out.
  * '`*`' separates elements of a tuple type.   
  * Process types are necessary in typechecking, but I think they are more or less useless. Process names do have a type, however ...  
  * The syntactic precedence of types is more or less as listed, or so I hope and intend. 
  * Explicit types are optional syntactically, as in ML and OCaml and Miranda and Haskell and all good strongly-typed languages. The typechecker infers them. It may be pragmatic to include them in the parameter list of a process definition, and in '`new`' channel declarations.
  * Type variables / unknown types `'`*x* and `''`*x* are for function definitions. As in ML, `''`*x* is an equality type.  
  * Classical types are everything except *qbit* or those involving *qbit* (but function, process and channel types are classical whatever their internal types).  
  * Equality types are everything except *qbit*, *qstate*, function, process and channel (or anything involving those).  

* Pattern *pat*

  | `_`  
  | `[]`  
  | `()`  
  | *constant*  
  | *x*  
  | `[` *pattern* `;` *pattern* ... `;` *pattern* `]`
  | *pat* `::` *pat*  
  | *pat* `,` ... `,` *pat*  
  | *pat* `:` *type*  
  | `(` *pat* `)`  

  * For constants see Expression *E* below.  Also, it seems, gates are allowed as constants.
  * Typed patterns *pat*`:`*type* often need bracketing. 
  * `let`, `E?..` and function parameters use a restricted form of pattern: only *x*, `_`, `()` and tuples thereof -- i.e. patterns which can't fail to match.
  
* Expression *E*

  | *constant*  
  | `_Phi(` *E* `)`  
  | *x*  
  | `if` *E* `then` *E* `else` *E* `fi`  
  | `if` *E* `then` *E* `elif` *E* `then` *E* ... `else` *E* `fi`  
  | `match` *E* `.` `+` *pat* . *E* ... `+` *pat* . *E*  
  | `(` *E* `,` ... `,` *E* `)`  
  | `[` *E* `;` ... `;` *E* `]`  
  
  | *E* *E*  
  | `-` *E*  
  | `not` *E*  
  | *E* `::` *E*  
  | *E* `@` *E*  
  | *E* *aop* *E*  
  | *E* *cop* *E*  
  | *E* *bop* *E*  
  | `lam` *pat* ... *pat* `.` *E*  
  
  * Constants are integers; chars `'c'`; strings `"chars"`; bit constants `0b1` and `1b1`; basis vectors`|0>`, `|1>`, `|+>` and `|->`; gates `_H`, `_CNot`, `_I`, `_X`, `_Y`, `_Z`, `_F` and `_G`.
  * The gate `_Phi(*E*)` is not a constant. (I suppose it is a constructor -- the only one so far.)  
  * The zero-tuple `()` and the empty list `[]` are special cases of the bracketed rules.
  * There is no one-tuple.   
  * Match expressions are parsed with the offside rule: the components can't start left of `match`, and the patterns and right-hand-side expressions have to be right of `+`. (They will one day disappear, I hope, in favour of Miranda-style matching on function parameters.)  
  * Function applications are *E* *E* -- juxtaposition. And of course left associative, so that *E* *E* *E* is (*E* *E*) *E*.  There's a function library (see below) and perhaps one day there will be downloadable bundles of functions.  
  * Absolutely no process stuff, no manipulation of qbits. But see *print_string*, *print_strings* and *print_qbit* below.  
  
* Built-in operators  
    
    * `@` (append) was an operator in one of Gay & Nagarajan's examples; it's still included.  
    * `::` (cons) is now included.  
    * `+`, `-`, `*`, `/` arithmetic operators *aop*.  
    * `<`, `<=`, `=`, `<>`, `>=`, `>` comparison operators *cop*.
    * `&&`, `||`, boolean operators *bop*.
    
* Process name *N*

  Starts with an upper-case letter, continues with alphanumeric, prime and underscore.
  
* Variable name *x*

  Starts with a lower-case letter, continues with alphanumeric, prime and underscore. (Actually, it seems, you can get away with upper case, but names in function definitions have to start with lower case.)

## Input-Output channels, *show* and *qval*

There's an input channel *in*

  * *in*: ^*string*
  
It reads a single line of input as a string. Writing to it is a run-time error, because I don't know how to typecheck receive-only channels.

There are functions which print out strings and *qstates*. But it's inelegant to use them in a process. So there are output channels.

  * *out*: ^*string list*
  * *outq*: ^*qstate*

outq is peculiar for peculiar reasons. There can't be an output channel which takes qbits, because if you send a qbit down a channel, you lose it. So there's a special type *qstate*, the result of *qval*: *qbit* -> *qstate*, which is a classical value that can be sent down a channel. To ensure no computational cheating, there's nothing else you can do with a *qstate* value. 

Reading from an output channel is a runtime error, because I don't know how to typecheck send-only channels.

To help with output, there is the special function *show*

  * *show*: ''*a* -> *string*
  
-- it takes any *equality* value and turns it into a string. Obviously it shouldn't have anything to do with qbits or qstates (or there could be computational cheating), but it couldn't do anything for functions, processes, qstates and channels either.

For qbits there is *qval*

  * *qval*: *qbit* -> *qstate*

The use of *qval* is connected to the *outq* channel: *outq*!(*qval* *q*) prints a string *q*`:`*V*, the qbit's index *q* and a representation *V* of its state as a probability vector in the computational basis.

## Probability vectors and symbolic calculation

Qtpi uses a symbolic quantum calculator: only at the point of measurement does it calculate numerically. This enables it to do some nice tricks, like 'teleporting' an unknown qbit.

Qbits are represented as integer indices into a quantum state of probability vectors in the computational basis defined by `|0>` and `|1>`. An unentangled qbit indexes a pair of probability expressions (*A*, *B*) representing (*A*`|0>`+*B*`|1>`). A singly-entangled qbit indexes a quadruple (*A*,*B*,*C*,*D*), representing \[*i*; *j*\](*A*`|00>`+*B*`|01>`+*C*`|10>`+*D*`|11>`), where *i* and *j* are the indices of the entangled qbits (some of *A*, *B*, *C* and *D* will be zero, of course). And so on for larger entanglements.

The constant `h` is *sqrt*(1/2), and `h(`*k*`)` means `h`<sup>*k*</sup>.  *h* is also *cos*(&pi;/4) and *sin*(&pi;/4). The constant `f` is *sqrt*((1+`h`)/2), which is *cos*(&pi;/8), and `g` is *sqrt*((1-`h`)/2), which is *sin*(&pi;/8).

An unknown qbit with index *i* starts life as the vector (`a`<sub>i</sub>`|0>`+`b`<sub>i</sub>`|1>`), and the evaluator knows that `a`<sub>i</sub><sup>2</sup>+`b`<sub>i</sub><sup>2</sup>=1.

## Gates

For weasely syntactic reasons, gate names start with an underscore. We recognise the following (for meaning of `f`, `g` and `h`, see above). All arity 1, except `_Cnot` which is arity 2.

  * `_H`: the Hadamard gate, takes `|0>` to `h|0>+h|1>`, `|1>` to `h|0>-h|1>`. A kind of 45&deg; rotation (&pi;/4).
  * `_F`: takes `|0>` to `f|0>+g|1>`, `|1>` to `g|0>-f|1>`. A kind of 22.5&deg; rotation (&pi;/8).
  * `_G`: takes `|0>` to `g|0>+f|1>`, `|1>` to `f|0>-f|1>`. A kind of 67.5&deg; rotation (3&pi;/8).
  * `_I`: takes `|0>` to `|0>`, `|1>` to `|1>`. Identity.
  * `_X`: takes `|0>` to `|1>`, `|1>` to `|0>`. Exchange, inversion, not.
  * `_Z`: takes `|0>` to `-|1>`, `|1>` to `|0>`. (dunno what to call it.)
  * `_Y`: takes `|0>` to `-|1>`, `|1>` to `|0>`. (dunno what to call it, but equivalent to the product `_Z_X`).
  * `_Cnot`: takes `|00>` to `|00>`, `|01>` to `|01>`, `|10>` to `|11>`, `|11>` to `|10>`. (Controlled-not).
  * `_Phi(`*i*`)`: *i*=0 is `_I`; *i*=1 is `_X`; *i*=2 is `_Z`; *i*=3 is `_Y`.

We don't yet have gate multiplication in the language. Nor tensor product. We should have both, I think.

## The *dispose* channel

Qbits get discarded: Alice sends one to Bob, Bob receives it, measures it, remembers the result, and then waits for the next one. The qbit is destroyed on detection, and it vanishes from the simulation. A vanished qbit is in fact recycled: not quite garbage-collected, because conventional garbage collection doesn't understand how qbits work.

Before I realised that qbits are destroyed on detection, I implemented a *dispose* channel of qbits (and it still exists because perhaps sometimes it might be needed). Send a qbit down the *dispose* channel and it has gone. It will be made available to be recycled, unless it is entangled, in which case it may be made available later if the entanglement collapses, or unknown, in which case it will be forever in limbo. Like any sent-away qbit, you can't use it once it's disposed (see [the resourcing document](./ownership.html) for explanation).

Reading from from the *dispose* channel is a run-time error, once again because I don't know how to typecheck send-only channels.

<a name="restrictions"></a>
## Restrictions

Qbits are big fragile things. They are sent through gates, transmitted through channels, measured. Protocol descriptions (e.g. QKD) talk of processes sending qbits to each other and separately communicating information like basis and value over classical channels. So although in principle you might be able to make lists of qbits, tuples of qbits and the like, for simplicity of description of protocols I impose restrictions which means that anything other than single qbits are useless. This also massively simplifies *resourcing*: see [the resourcing document](./ownership.html) for explanation.

These restrictions give you a language in which qbits are known only by a single name at any time. This simplifies the description of protocols, I believe, and it simplifies resource-checking, but it's really there for aesthetic reasons.

It is also impossible to branch according to the state or identity of a qbit. (In unsimulated real life you couldn't ...). Likewise on the identity or equality of a function or a process.

  * **A channel is either `^qbit` or `^classical`**.
    	
  * **A process argument is either `qbit`, or classical**.
  
  	Note that a channel is a classical value, whatever its type. So is a function or a process.
  
  * **No qbit-valued conditionals as  process argument or send argument**.
  
  	Conditionals include `if` and pattern-matching. It's ok to have qbit-valued conditionals in other positions, such as
  	
  			if a=0 then q1 else q2 fi >> _H

  * **`let` and pattern-matching can only bind classical values**.
  
  	This is a surprising restriction, because I included pattern matching in qtpi precisely to make it safe to bind qbits, and indeed the resource-checker can cope with it. But I think it's a better language without it.
    
  * **A function has classical arguments and delivers a classical result**.
  
  	Without the result restriction resource-checking simply wouldn't work. Without the argument restriction some computational cheating could occur: e.g. a process could get the qstate of another process's qbit. (Because of the next restriction that cheating would do you no good, but it would still feel wrong.)
  	
  	There is a loophole: this restriction is applied to function *definitions*. This is to allow library functions (currently qval and show) to take non-classical arguments. But see restriction on library functions below (oh dear).

  * **No comparison of qbits, qstates, or values containing qbits or qstates**.
  
  	This stops programs doing anything, apart from quantum measurement, to branch on the value or identity of a qbit.
  
  * **No comparison of functions, processes or channels, or values containing functions, processes or channels**.
  
  	Restriction on function comparison is standard in functional programming. You can't compare function values, because they are infinite. Ditto processes (which may one day arise as computational values: they are already a type). Channel comparison seems dodgy too, so I prohibit it.
  
  * **Library functions don't expose simulation state**.
  
  	There used to be a function *qbit_state* which gave you a string representation of a qbit's internal state. Useful for diagnostic printing, I thought. Then I realised it allowed the program to branch on whether a pair of qbits are entangled or not, by comparing the results of *qbit_state* on them. Horror!
  	
  	Not all is lost: there's *qval* which gives a *qstate*, there's the *outq* channel which accepts a *qstate*, and the `-verbose qsim` switch on Qtpi allows you to watch the simulation in any case.
  	
  	This is a restriction on the implementation of the language. Not sure how to police it ... especially if I allow downloadable libraries. Hmm.
  	
## Interface functions

We need to be able to read and write stuff: reading to give initial values like how many qbits to create; writing to describe results. It's also useful to include some functions to deal with lists and tuples. 

**But**, *but*, but. Functions take classical arguments and deliver classical results -- i.e. they have nothing to do with qbits. See restrictions above.

The library is mostly inspired by Miranda and/or Bird & Wadler's "Introduction to Functional Programming". Easy to add more (see the file library.ml). Note that argument types *'a*, etc., are classical.

Following the introduction of the *num* type in place of the old *int*, we can have fractional numbers. But several of the library functions insist on non-fractional arguments: *bitand*, *drop*, *nth*, *num2bits*, *randbits*, *tabulate*, *take*. If this causes a problem, use *floor*, which converts fractions to integers.
    
  * *abandon*: *string* -> *'a*  
	* stops the program and doesn't return (raises an exception).  
  * *append*: *'a list* -> *'a list* -> *'a list*
  * *concat*: *'a list list* -> *'a list*
  * *const*: *'a* -> *'b* -> *'a*
  * *drop*: *num* -> *'a list* -> *'a list*
  * *dropwhile*: (*'a* -> *bool*) -> *'a list* -> *'a list*
  * *exists*: (*'a* -> *bool*) -> *'a list* -> *bool*
  * *filter*: (*'a* -> *bool*) -> *'a list* -> *'a list*
  * *floor*: *num* -> *num*
  * *foldl*: (*'a* -> *'b* -> *'a*) -> *'a* -> *'b list* -> *'a*
  * *foldr*: (*'a* -> *'b* -> *'b*) -> *'b* -> *'a list* -> *'b*
  * *forall*: (*'a* -> *bool*) -> *'a list* -> *'a list*
  * *fst*: *'a*\**'b* -> *'a*  
  * *hd*: *'a list* -> *'a*  
	  * raises an exception if applied to `[]`  
  * *iter*: (*'a* -> *'b*) -> *'a list* -> *unit*
  * *length*: *'a list* -> *num*  	
  * *map*: (*'a* -> *'b*) -> *'a list* -> *'b list*
  * *max*: *num* -> *num* -> *num*
  * *min*: *num* -> *num* -> *num*
  * *nth*: *'a list* -> *num* -> *'a*
  * *qval*: *qbit* -> *qstate*
  * *randbits*: *num* -> *bit list*
  * *rev*: *'a list* -> *'a list*
  * *show*: *''a* -> *string*
	  * converts a value to a string. Takes an equality type, because it couldn't give interesting results if applied to a qbit, a function, process, channel or qstate.  
  * *sort*: *'a list* -> *'a list*
	  * sorts in ascending order
  * *snd*: *'a*\**'b* -> *'b*  
  * *tabulate*: *num* -> (*num* -> *'a*) -> *'a list*
  * *take*: *num* -> *'a list* -> *'a list*
  * *takewhile*: (*'a* -> *bool*) -> *'a list* -> *'a list*
  * *tl*: *'a list* -> *'a list*  
	  * raises an exception if applied to `[]`  
  * *unzip*: *'a*\**'b* *list* -> *'a* *list* \* *'b* *list*
  * *zip*: *'a* *list* -> *'b* *list* -> *'a*\**'b* *list*
	  * raises an exception if applied to lists of differing lengths (but probably shouldn't)
  * 
  * *bitand*: *num* -> *num* -> *num*
  * *bits2num*: *bit list* -> *num*
  * *num2bits*: *num* -> *bit list*
  * 
  * *read_alternative*: *string* -> *string* -> (*string*\**'a*) *list* -> *'a*
	  * *read_alternative* *prompt* "/" [(*s0*,*v0*);(*s1*,*v1*);...] prints *prompt*(*s0*/*s1*/...) and returns *v0* or *v1* or ... according to what the user types
  * *read_bool*: *string* -> *string* -> *string* -> *bool*
	  * prompt, true\_response, false\_response
  * *read_num*: *string* -> *num*
  * *read_string*: *string* -> *string*
	  * *read_int* and *read_string* take a prompt-string argument.  
  * 
  * *print_qbit*: *qbit* -> *unit*
	  * *print_qbit* *q* has the same effect as *outq*!(*qval* *q*)
  * *print_string*: *string* -> *unit*
	* *print_string* *E* has the same effect as *out*!\[*E*\]
  * *print_strings*: *string list* -> *unit*
	* *print_strings* *Es* has the same effect as *out*!*Es*

