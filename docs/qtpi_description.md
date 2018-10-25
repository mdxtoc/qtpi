# qtpi language description

Based on CQP (Gay & Nagarajan, POPL 2005) and therefore on the pi calculus. Some changes cosmetic (e.g. fewer square brackets, fewer capital letters); some for convenience (no mandatory types, because there's a typechecker); some because state-changing operations (e.g. applying unary gates, measurement) should be protocol steps; new operators intended to be easy to read.

The expression language is moving closer to Miranda: '`where`' clauses, offside parsing and, eventually, laziness. The process language is beginning to exploit the offside parser and maybe I've gone too far with the parallel, sum and match constructs.

## The offside rule

Most languages use lots of brackets in their syntax. You often have to use brackets in OCaml, for example, around the stuff between `then` and `else`, because the `else` part can be missing (i.e. no closing bracket for `then`) and likewise after the `else` because there's no closing `fi`.

When I began to implement Qtpi I thought that I'd do the Algol 68 thing and include `fi`. When I realised I needed pattern matching, I introduced a construct which started `match` and ended `hctam`. It looked horrible.

Landin's *offside rule* makes closing brackets unnecessary. In the Miranda expression *E* `where` *E'*, *E'* mustn't be left of `where`, and can't be left of its own first token. This disambiguates things like 

		hwc key message
		  where message = packets [] bits
		                    where bits = f message
		                    where f = g k
		  where key = ...
	
-- the first and fourth `where`s attach to hwc key message; the second and third attach to packets [] bits.

It's tricky to make an offside parser, but I'm trying. So far it applies to `where` clauses, to `match`es in processes and expressions, and to parallel process compositions.

## Grammar 

Processes *P*, input-output steps *IO*, quantum steps *Q*, expressions *E*, types *T*, process names *N*, variable names *x*, parameters *par*, patterns *pat*, gate expressions *G*. Square brackets surround optional elements.

* Program description

	A program is a sequence of process and function definitions. One of the process descriptions must be `System`, which must have no parameters.

  | `proc` *N* `(`  *par*  `,`  ... `,` *par* `)` = *P*  
  | `fun` *x* *pat* ... *pat*  = *E*  
  | `fun` *x* *pat* ... *pat* `:` *T* = *E*  
  
  * Types are optional in process parameters, but it seems to be pragmatic to include them.
  * None of the process parameters can be a process.
  * As with `let` and with reads `E?(pat)`, function parameters are bullet-proof patterns: no constants, no lists.
  * Function parameters may include a type, and the result type of the function may be given. This allows you to define functions with types like `bit list -> 'a list -> 'a list`.
  
* Process *P* 

  | *Q* `.` *P*  
  | `+` *IO* `.` *P* ... `+` *IO* `.` *P*   
  | `|` *P* ... `|` *P*   
  | `if` *E* `then` *P* `else` *P* `fi`  
  | `match` *E* `.` `+` *pat* `.` *P* ... `+` *pat* `.` *P*   
  | `( new` *par*  `,`  ... `,` *par* `)` *P*   
  | `( newq` *par* [ `=` *E* ] `,`  ... `,` *par* [ `=` *E* ] `)` *P*  
  | `( let` *pat* `=` *E* `)` *P*  
  | `{` *E* `}` `.` *P*  
  | *N* `(` *E*  `,`  ... `,` *E*  `)`  
  | `(` *P* `)`  
  | `_0`

  * Note that a a guarded sum starts with a `+`, and a parallel composition starts with a `|`. Neither needs to be bracketed, because the offside parser ensures that everything is to the right of the `+` or `|`, as appropriate.  
  * match processes also use the `+` separator.  
  * `new` creates channels, as in the pi calculus &nu;.    
  * `newq` creates qbits. Initialisation to basis vectors is optional (without it you get (*a*`|0>`+*b*`|1>`), for unknown *a* and *b*, where *a*<sup>2</sup>+*b*<sup>2</sup>=1.  
  * `let` expressions use a restricted form of pattern -- no constants, no lists -- so they can't fail to match.  
  * `_0` is the null process (i.e. termination). I would have used `()` (null parallel or null guarded sum: same difference) but it would have caused parsing problems.  
  * `{` *E* `}` `.` *P* lets you execute an arbitrary expression, but it has to be unit type. Useful for outputting strings and the like.  
  * You can execute an arbitrary expression via a 'let' binding, if you wish.  Very non-pi if you write `(let _ =` *E*`)`. Sorry.
  
* Quantum step *Q*
  
  | *E* `,` *E* `,` ... `,` *E* `>>` *G*    
  | *E* `=?` (*par*)    
  | *E* `=?` `[` *E* `]` (*par*)    

  * '`>>`' is 'send through a gate'; each left-hand *E* must describe a single qbit. The arity of the input tuple must match the arity of the gate (e.g. _H takes one qbit, _Cnot takes 2, _Fredkin if we had it would take 3, and so on).  
  * `=?` is measure, in the computational basis defined by `|0>` and `|1>`.  The parameter *par* binds the single-bit result. 
  * The optional square-bracketed *E* is a gate expression controlling the measurement basis: `_H` causes measurement in the Hadamard basis, and `_I` causes the computational basis. (Other gates and thus bases may follow :-).) Internally `q=?[G](b)` is equivalent to `q>>G . q=?(b) . q>>G`.  
  * CQP had `*=` for measure, which looked like an assignment, so I changed it to `=?`.   

* Input-output step *IO*  

  | *E* `?` `(` *pat* `)`    
  | *E* `?` `_`    
  | *E* `!` *E*    

  * '`?`' is read, as in many implementations of the pi calculus: *E* is a channel; the pattern is bracketed, as is the name in the pi calculus. The pattern is restricted as in a `let`  binding -- no constants except `()`, no lists.   
  * *E*`?_` ignores the value it reads (should I allow this? I'm not sure).  
  * '`!`' is write, as in many implementations of the pi calculus: the first *E* is a channel; the output expression can of course be an unbracketed tuple. (Miranda style says tuples must be bracketed: not this one.)  
  * Channels each carry either a qbit or a classical value (one not including any qbits).  
  
* Parameter *par*

  | *x*  
  | *x* `:` *T* 
  
  * Parameter type specs are optional, always.
  
  
* Type *T* 

  | `qbit`  
  | `unit`  
  | `int`  
  | `bool`  
  | `bit`  
  | `Range` *int*`:` *int*  
  | `string`  
  | `char`  
  | `basisv`  
  | `'`*x*  
  | *T* `list`  
  | *T* `*` ... `*` *T*  
  | `^` *T*  
  | *T* `->` ... `->` *T*  
  | *T* `process`  
  | `(` *T* `)`  

  * These types are still ML style. Miranda style is neater (`[int]` rather than `int list`, `(int,bit)` rather than `int*bit`, and they don't need syntactic precedence. One day soon ...)  
  * Range types were in original CQP. They are hard to deal with in the typechecker and are currently pretty useless, but with a subtyping typechecker they may come back (I do hope so).  
  * `basisv` is the type of basis vectors (see below).  
  * '`*`' separates elements of a tuple type.   
  * Process types *T* `process` are currently for internal use.  
  * The syntactic precedence of types is more or less as listed, or so I hope and intend. 
  * Explicit types are optional syntactically, as in ML and OCaml and Miranda and Haskell and all good strongly-typed languages. The typechecker infers them. It's probably pragmatic to include them in the parameter list of a process definition, and in '`new`' channel declarations.

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

  * For constants see Expression *E* below.  
  * Typed patterns *pat*`:`*type* often need bracketing. 
  * `let`, `E?..` and function parameters use a restricted form of pattern: only `x`, `_`, `()` and tuples thereof -- i.e. patterns which can't fail to match.
  
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
  
  * Constants are integers; chars `'c'`; strings `"chars"`; bit constants `0b1` and `1b1`; basis vectors`|0>`, `|1>`, `|+>` and `|->`; gates `_H`, `_CNot`, `_I`, `_X`, `_Y`, `_Z`.
  * The gate `_Phi(*E*)` is not a constant. (I suppose it is a constructor -- the only one so far.)  
  * The zero-tuple `()` and the empty list `[]` are special cases of the bracketed rules.
  * There is no one-tuple.   
  * Match expressions are parsed with the offside rule: the components can't start left of `match`, and the patterns and right-hand-side expressions have to be right of `+`. (They will soon disappear in favour of Miranda-style matching on function parameters.)  
  * Function applications are *E* *E* -- juxtaposition. And of course left associative, so that *E* *E* *E* is (*E* *E*) *E*.  There's a function library (see below) and Real Soon Now there will be downloadable bundles of functions.  
  * Absolutely no process stuff, no manipulation of qbits. But see *print_string*, *print_strings* and *print_qbit* below.  
  
* Built-in operators  
    
    * `@` (append) was an operator in one of Gay & Nagarajan's examples.  
    * `::` (cons) is now included.  
    * `+`, `-`, `*`, `/` arithmetic operators *aop*.  
    * `<`, `<=`, `=`, `<>`, `>=`, `>` comparison operators *cop*.
    * `&&`, `||`, boolean operators *bop*.
    
* Process name *N*

  Starts with an upper-case letter, continues with alphanumeric, prime and underscore.
  
* Variable name *x*

  Starts with a lower-case letter, continues with alphanumeric, prime and underscore.

## The *dispose* channel

Qbits get discarded: Alice sends one to Bob, Bob receives it, measures it, and then waits for the next one. Garbage collection might be possible, but it would have to understand the central quantum state which deals with every qbit ever created and, in particular, deals with entanglements.

Learning from my experience of separation logic, I implemented a *dispose* channel of qbits. Send a qbit down the *dispose* channel and it has gone. It will be made available to be recycled, unless it is entangled, in which case it may be made available later. Like any sent-away qbit, you can't use it once it's disposed (see [the resourcing document](./ownership.html) for explanation).

Because I don't yet  know how to add one-way channels to the language, if you read from the *dispose* channel you get a new qbit. Ho ho?

## Output channels

If I added output channels I could probably (no, certainly) get rid of the braced protocol step `{`*E*`}`, which only seems to be useful for printing stuff. So I shall do that soon.

<a name="restrictions"></a>
## Restrictions

Qbits are big fragile things. They are measured, sent through gates, transmitted through channels. Protocol descriptions (e.g. QKD) talk of processes sending qbits to each other and separately communicating information like basis and value over classical channels. So although you are able to make lists of qbits, tuples of qbits and the like, for simplicity of description of protocols, because of these restrictions you cannot do anything with them. This also massively simplifies *resourcing*: see [the resourcing document](./ownership.html) for explanation.

These restrictions, then, attempt to give you a language in which qbits are known only by a single name at any time. This simplifies the description of protocols, I believe, and it simplifies resource-checking, but it's really there for aesthetic reasons.

It is also impossible to branch according to the state or identity or equality of a qbit. (In unsimulated real life you couldn't ...). Likewise the identity or equality of a function.

  * **A channel is either `^qbit` or `^classical`**.
    	
  * **A process argument is either `qbit`, `^qbit`,  or classical**.
  
  * **No qbit-valued conditionals as  process argument or send argument**.
  
  	Conditionals include `if` and pattern-matching. It's ok to have qbit-valued conditionals in other positions, such as
  	
  			if a=0 then q1 else q2 fi >> _H

  * **`let`, and pattern-matching in processes, can only bind classical values**.
  
  	Pattern-matching in expressions seems to be ok. Will know when we have a Coq proof.
  
  * **A function application can only deliver a classical value**.

  * **No comparison of qbits, or values containing qbits**.
  
  	Given the other restrictions, such comparisons would be more or less useless anyway.
  
  * **No comparison of functions, or values containing functions**.
  
  	This is standard in functional programming. You can't compare function values, because they are infinite.
  
  * **Library functions don't expose simulation state**.
  
  	There used to be a function *qbit_state* which gave you a string representation of a qbit's internal state. Useful for diagnostic printing, I thought. Then I realised it allowed the program to branch on whether a pair of qbits are entangled or not, by comparing the results of *qbit_state* on them. Horror!
  	
  	Not all is lost: there's *print_qbit*, and the `-verbose qsim` switch on Qtpi allows you to watch the simulation.
  	
  	This is a restriction on the implementation of the language. Not sure how to police it ... especially if I allow downloadable libraries. Hmm.
  	
## Interface functions

We need to be able to read and write stuff: reading to give initial values like how many qbits to create; writing to describe results. It's also useful to include some functions to deal with lists and tuples. 

**But**, *but*, but. Functions can't deliver qbits or values containing qbits. See restrictions above.

Mostly inspired by Miranda and/or Bird & Wadler's "Introduction to Functional Programming". Easy to add more (see the file library.ml). The list and pair functions do what you'd expect (but you can't use them to deliver qbits: see restriction above). Note the restriction on revealing state above.
    
* *abandon*: *string* -> *'a*  
	* stops the program and doesn't return (raises an exception).  
* *append*: *'a list* -> *'a list* -> *'a list*
* *concat*: *'a list list* -> *'a list*
* *const*: *'a* -> *'b* -> *'a*
* *drop*: *int* -> *'a list* -> *'a list*
* *dropwhile*: (*'a* -> *bool*) -> *'a list* -> *'a list*
* *exists*: (*'a* -> *bool*) -> *'a list* -> *bool*
* *filter*: (*'a* -> *bool*) -> *'a list* -> *'a list*
* *foldl*: (*'a* -> *'b* -> *'a*) -> *'a* -> *'b list* -> *'a*
* *foldr*: (*'a* -> *'b* -> *'b*) -> *'b* -> *'a list* -> *'b*
* *forall*: (*'a* -> *bool*) -> *'a list* -> *'a list*
* *fst*: *'a*\**'b* -> *'a*  
* *hd*: *'a list* -> *'a*  
	* raises an exception if applied to `[]`  
* *iter*: (*'a* -> *'b*) -> *'a list* -> *unit*
* *length*: *'a list* -> *int*  	
* *map*: (*'a* -> *'b*) -> *'a list* -> *'b list*
* *max*: *int* -> *int* -> *int*
* *min*: *int* -> *int* -> *int*
* *nth*: *'a list* -> *int* -> *'a*
* *rev*: *'a list* -> *'a list*
* *show*: *'a* -> *string*
	* converts any value to a string. If you use it on a qbit or a function you won't see anything interesting.  
* *sort*: *'a list* -> *'a list*
	* sorts in ascending order; shouldn't sort functions and qbits (but probably does)
* *snd*: *'a*\**'b* -> *'b*  
* *tabulate*: *int* -> (*int* -> *'a*) -> *'a list*
* *take*: *int* -> *'a list* -> *'a list*
* *takewhile*: (*'a* -> *bool*) -> *'a list* -> *'a list*
* *tl*: *'a list* -> *'a list*  
	* raises an exception if applied to `[]`  
* *unzip*: *'a*\**'b* *list* -> *'a* *list* \* *'b* *list*
* *zip*: *'a* *list* -> *'b* *list* -> *'a*\**'b* *list*
	* raises an exception if applied to lists of differing lengths (but probably shouldn't)
* 
* *bitand*: *int* -> *int* -> *int*
* *bits2int*: *bit list* -> *int*
* *int2bits*: *int* -> *bit list*
* 
* *read_alternative*: *string* -> *string* -> (*string*\**'a*) *list* -> *'a*
	* *read_alternative* *prompt* "/" [(*s0*,*v0*);(*s1*,*v1*);...] prints *prompt*(*s0*/*s1*/...) and returns *v0* or *v1* or ... according to what the user types
* *read_bool*: *string* -> *string* -> *string* -> *bool*
	* prompt, true\_response, false\_response
* *read_int*: *string* -> *int*
* *read_string*: *string* -> *string*
	* *read_int* and *read_string* take a prompt-string argument.  
* 
* *print_qbit*: *qbit* -> *unit*
	* prints a string *q*`(`*A*`|0>`+*B*`|1>)`, the qbit's index *q* and a representation of its state as a probability vector in the computational basis. In probabilities the constant `h` means *sqrt*(1/2), and `h(`*k*`)` means (*sqrt*(1/2))<sup>*k*</sup>. If *q* is entangled with *q'* you will see stuff like `[`*q*;*q'*`](`*A*`|00>`+*B*`|01>+`*C*`|10>`+*D*`|11>)`. The standard example would be `[0,1](h|00>+h|01>)`. And so on for larger entanglements.
* *print_string*: *string* -> *unit*
* *print_strings*: *string list* -> *unit*


