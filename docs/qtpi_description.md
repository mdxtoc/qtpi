(I used to distribute an html version of this file. But git's rendering is better than a browser's, so now it's exclusively at

        https://github.com/mdxtoc/qtpi/blob/master/docs/qtpi_description.md

But if you are reading it you know that already ...)

# qtpi core language description

Qtpi is a programming notation and its implementation. It allows simulation of quantum computation, and in particular simulation of multi-agent protocols. The language is a development of CQP (Gay & Nagarajan, POPL 2005), and therefore owes much to the pi calculus. Some developments are cosmetic (e.g. fewer square brackets in programs, fewer capital letters); some are for convenience (e.g. no mandatory types, because there's a typechecker); some because I felt that quantum operations (applying gates, measurement) should be protocol steps; and some are to clarify intricate computation (e.g. qubit collections, iterative subprocesses).

The notation uses process-calculus notation for the quantum calculations and for process communication, and functional notation for classical calculations. The functional notation at first was ML-like and has moved closer to Miranda: '`where`' clauses, offside parsing and, perhaps eventually, laziness. The process language is beginning to exploit the offside parser. I'm not actively pursuing either of those avenues at present.

## Core language and additions

The language described in this document is a mildly tweaked version of CQP. Separate documents describe additions:  

  * *logging sub-processes*, which allow you to attach output statements to a process without obscuring its content;  
  * *iterative sub-processes*, which can simplify the description of some algorithms;  
  * *qubit collections*, which allow you to simulate algorithms that deal with vectors of qubits. 

## Qubit or qbit?

The world uses 'qubit' for 'quantum bit'. CQP used 'qbit' for the simulated qubits a program manipulates, and at first qtpi did the same. Qbit actually would be a better name, because 'qubit' seems to be be pronounced 'q bit'. But it's too late to change the world's mind, and qtpi now uses 'qubit' (though it accepts 'qbit' in programs, because why not?).

## The offside parsing rule

Most languages use lots of brackets in their syntax. You sometimes have to use brackets in OCaml, for example, around the stuff after `then`, when there is no `else` to bracket it, and likewise after the `else` because there's no bracket to match `if`.

When I began to implement Qtpi I thought that I'd do the Algol 68 thing and use `if then else fi`. When I realised I needed pattern matching, I introduced a construct which started `match` and ended `hctam`. It looked horrible, and I could never remember how to spell hcatm.

Landin's *offside rule* often makes closing brackets unnecessary. In the Miranda expression *E* `where` *E'*, `where` mustn't be left of *E* and *E'* mustn't be left of `where`. This disambiguates things like 

		hwc key message
		  where message = packets [] bits
		                    where bits = f message
		                    where f = g key
		  where key = ...
	
-- the first `where` attaches to `hwc key message`; the second and third attach only to `packets [] bits`; the fourth attaches to everything.

So far the offside parser applies to function definitions (expression to the right of '='), to `where` clauses, to `match`es in processes and expressions, to guarded sums, to parallel process compositions and to conditionals. In conditionals `fi` is optional (but offside parsing is not).

The parser, as currently implemented, can generate *awful* error messages: 'syntax error at line k character j' sort of thing. This is shameful and when combined with offside parsing can prompt hair tearing. I'm sorry, I'm ashamed, and I really will fix it one day. I blame Donald Knuth and the automatic parser generators that he enabled.

## Optional typing

Qtpi has an automatic typechecker, so types are optional. Well, mostly optional -- arithmetic operators are very highly overloaded, to allow matrix arithmetic, so sometimes explicit typing is necessary to resolve ambiguities.

If you prefer explicit typing:  

  * parameters can be typed -- *x* `:` *T*
  * patterns *pat* and *bpat* can be typed but will usually need bracketing -- `(` *pat* `:` *T* `)` and `(` *bpat* `:` *T* `)` 
  * function definitions can be typed a la ML -- *f* *bpat* ... *bpat* `:` *T* = *E*  where *T* is the result type and the patterns can be separately typed  
  * expressions *E* can be typed if bracketed -- `(` *E* `:` *T* `)`

For clarity I've omitted typing from the syntax description below.

## Grammar 

Processes *P*, input-output steps *IO*, quantum steps *Q*, expressions *E*, types *T*, process names *N*, variable names *x*, parameters *par*, patterns *pat*, gate expressions *G*. Square brackets surround optional elements.

* Program *prog*

	A program is a sequence of process, function and value definitions. Process and function definitions are arranged in mutually-recursive groups. 

    | `proc` *pdef* ... *pdef* *prog*  
    | `fun` *fdef* ... *fdef* *prog*  
    | `let` *bpat* `=` *E*  
    
    * *E* must compute a classical value (nothing to do with qubits), but may call upon earlier function definitions. 
  
* Process definition *pdef*
  
    | *N* `(`  *x*  `,`  ... `,` *x* `)` = *P*  
  
  * There is a convention that process names *N* should start with an upper-case (capital) letter.  
  * One of the process descriptions must be `System`, which must have no parameters.  

* Function definition *fdef*

    | *f* *bpat* ... *bpat*  = *E*  
  
  * There is a convention that function names *f* start with a lower-case letter. 
  * The result of a function must be entirely classical -- i.e. have nothing to do with qubits.
    
* Process *P* 

    | *Q* `.` *P*  
    | *IO* `.` *P*  
    | `+` *IO* `.` *P* ... `+` *IO* `.` *P*   
    | `|` *P* ... `|` *P*   
    | `if` *E* `then` *P* `else` *P* `fi`  
    | `match` *E* `.` `+` *pat* `.` *P* ... `+` *pat* `.` *P*   
    | `( new` *par*  `,`  ... `,` *par* `)` *P*   
    | `( newq` *par* [ `=` *E* ] `,`  ... `,` *par* [ `=` *E* ] `)` *P*  
    | `( let` *bpat* `=` *E* `)` *P*  
    | *N* `(` *E*  `,`  ... `,` *E*  `)`  
    | `(` *P* `)`  
    | `_0`  
    | `.` *P*  

  * A guarded sum starts with a `+`, and a parallel composition starts with a `|`.[^1] Neither needs to be bracketed, because the offside parser ensures that everything is to the right of the `+` or `|`, as appropriate.  
  * `match` also uses the `+` separator, and uses the offside parser.  
  * `new` creates channels, like the pi calculus &nu;.    
  * `newq` creates qubits. Initialisation to a ket is optional (without it you get (*a<sub>k</sub>*`|0>`+*b<sub>k</sub>*`|1>`), for complex-valued unknowns *a<sub>k</sub>* and *b<sub>k</sub>*, where |*a<sub>k</sub>*|<sup>2</sup>+|*b<sub>k</sub>*|<sup>2</sup>=1).  
  * `_0` is the null process (i.e. termination). I would have used `()` (null parallel or null guarded sum: same difference) but it would have caused parsing problems.  
  * `{` *E* `}` `.` *P*, part of CQP, is no longer included. It had become used exclusively for printing, and the output channels `out` and `outq` now do the job.  
  * If it helps your description, you can include extra `.` separators.
  * There are also additions to deal with logging output, with qubit collections, and with iterative processes. Those are dealt with in separate documents.  

[^1]: this is a major departure from pi calculus syntax. I hope that offside parsing makes it worthwhile.
  
* Quantum step *Q*
  
    | *E* `,` *E* `,` ... `,` *E* `>>` *G*    
    | *E* `⌢̸` (*bpat*)    
    | *E* `⌢̸` `[` *E* `;` ... `;` *E* `]` (*bpat*)    

  * '`>>`' is 'send through a gate'; each left-hand *E* must describe a single qubit. The arity of the input must match the arity of the gate (e.g. H takes one qubit, Cnot takes 2, Fredkin takes 3, and so on -- but for various reasons it's a run-time check).  
  * `⌢̸` is measure, in the computational basis defined by `|0>` and `|1>`.  The pattern *bpat* binds the single-bit result. 
  * The optional square-bracketed *E* list in a measurement is a gate expression controlling the measurement basis: for example `[H]` specifies measurement in the Hadamard basis, and `[I]` the computational basis. If there's more than one gate it specifies measurement in the basis defined by the matrix product of those gates. Internally `q-/-[G](b)` is equivalent to `q>>G . q-/-(b) . q>>G†` where `G†` is the conjugate transpose of `G`. (Somewhat more complicated if *q* is part of an entanglement, but the calculator deals with those complications.) 
  * CQP had `*=` for measure, which looked like an assignment, so (at Guillaume Poly's suggestion) I changed it to `=?`. And then I changed it to `-/-` to try to make it look like the meter symbol that's used in quantum circuit diagrams, and finally I discovered `⌢̸`.   

* Input-output step *IO*  

    | *E* `?` `(` *bpat* `,` ... `,` *bpat* `)`    
    | *E* `?` `_`    
    | *E* `!` *E*    

  * '`?`' is receive, as in many implementations of the pi calculus: *E* is a channel; the tuple of receive patterns must be bracketed, even if it is a one-tuple. Values read from the channel `E` are bound by the *bpat*s.   
  * '`!`' is send, as in many implementations of the pi calculus: the first *E* is a channel; the output expression can be an unbracketed tuple. (Miranda style says tuples must be bracketed: not this one. I blame Robin Milner.)  
  * Channels each carry either a qubit or a classical value (one not including any qubits). 
  * Channels can be buffered. The level of buffering is controlled with the `-chanbuf_limit` switch. (The default is no buffering - i.e. synchronised message-passing -- because I think it makes most sense with guarded commands).
    
* Type *T* 

    | `qubit`  
    | `unit`  
    | `num`  
    | `bool`  
    | `bit`  
    | `string`  
    | `char`  
    | `sxnum`  
    | `gate`  
    | `bra`  
    | `ket`  
    | `matrix`  
    | `qstate`  
    | `'`*x*  
    | `''`*x*  
    | `'*`*x*  
    | `[` *T* `]`  
    | `(`*T* `,` ... `,` *T* `)`  
    | `^` *T*  
    | *T* `->` ... `->` *T*  
    | *T* `process`  
    | `(` *T* `)`  

  * List and tuple types are Miranda style rather than ML style: `[`*T*`]` rather than *T* `list`; `(`*T1*`,`*T2*`)` rather than *T1*`*`*T2*. 
  *  '*num*' is the type of numbers: unbounded integers and unbounded-precision rationals (fractions), so that we can do proper arithmetic. Using *num* rather than *int* can cause some problems: some library functions, such as *take* and *drop*, really don't work with fractional arguments (or, at least, I can't decide what they should do), and you may have to make use of *floor*.
  * Range types are in CQP, but no longer in qtpi. They are hard to deal with in the typechecker and are currently pretty useless, but if I can make a subtyping typechecker they might come back.  
  * `bit` ought to be a subtype of `int`, but I can't force the typechecker to agree.
  * `sxnum` is the type of symbolic complex numbers, the values that qtpi's symbolic quantum calculator manipulates.
  * `bra` is the type of unitary row vectors; `ket` of unitary column vectors.
  * `matrix` is the type of matrices of `sxnum`. `gate` is the type of unitary square matrices.
  * `qstate` is the type of the result of the *qval* function (see below). It's a peek at the simulator state. But qstates can't be compared or manipulated in any way. The only useful thing you can do with a *qstate* is to send it down the outq output channel, which prints it out.
  * Process types are necessary in typechecking, but I think they are more or less useless.   
  * The syntactic precedence of types is more or less as listed, or so I hope and intend. 
  * Explicit types are optional syntactically, as in ML and OCaml and Miranda and Haskell and all good strongly-typed languages. The typechecker infers them. It may be pragmatic to include them in the parameter list of a process definition, and in '`new`' channel declarations. Since arithmetic operators have been overloaded to allow for matrix arithmetic, such pragmatism may now be more often required.
  * Type variables / unknown types `'`*x* and `''`*x* are for function definitions. `'`*x* is a classical type: no qubits. As in ML, `''`*x* is an equality type: no qubits, qstates, functions, processes, channels. `'*`*x* is an everything type (includes qubits). 
  * Classical types are everything except *qubit* or those involving *qubit* (but function, process and channel types are classical whatever their internal types).  
  * Equality types are everything except *qubit*, *qstate*, function, process and channel (or anything involving those).  
  * Channel types (types following `^`) are restricted: they may be qubit or they may be non-functional classical (no qubits, no functions).

* Bullet-proof pattern *bpat*

    | *x*  
    | `_`  
    | `()`  
    | `(` *bpat* `,` ... `,` *bpat* `)` 
    
    * *bpat* always matches. It's used in `let`, *fdef* and receive (`?`) patterns

* General pattern *pat*

  | `_`  
  | `[]`  
  | `()`  
  | *constant*  
  | *x*  
  | `[` *pattern* ... `;` *pattern* `]`
  | *pat* `::` *pat*  
  | `(` *pat* `,` ... `,` *pat* `)`  
  | `(` *pat* `)`  

  * For constants see Expression *E* below.  
  * Tuple patterns are always bracketed  
  
* Expression *E*

  | *constant*  
  | *x*  
  | `if` *E* `then` *E* `else` *E* `fi`  
  | `if` *E* `then` *E* `elif` *E* `then` *E* ... `else` *E* `fi`  
  | `match` *E* `.` `+` *pat* . *E* ... `+` *pat* . *E*  
  | `(` *E* `,` ... `,` *E* `)`  
  | `[` *E* `;` ... `;` *E* `]`  
  
  | *E* *E*  
  | `-` *E*  
  | `not` *E*  
  | *E* &dagger;  
  | *E* `::` *E*  
  | *E* `@` *E*  
  | *E* *aop* *E*  
  | *E* *cop* *E*  
  | *E* *bop* *E*  
  | `lam` *pat* ... *pat* `.` *E*  
  
  * Constants are 
    + integers
    + chars `'` char `'` with the escapes `\n`, `\r`, `\t` and even `\b` (why?)
    + strings `"` chars `"` with escapes as for chars 
    + bit constants `0b0` and `0b1`
    + ket constants `|0>`, `|1>`, `|+>` and `|->`
    + bra constants `<0|`, `<1|`, `<+|` and `<-|`0 
    + (and longer bras and kets like `<-++|` or `|0100>`)
    + sxnum constants `sx_0`, `sx_1`, `sx_i`, `sx_h`, `sx_f` and `sx_g`.
  * The zero-tuple `()` and the empty list `[]` are special cases of the bracketed rules.
  * There is no one-tuple.   
  * Tuples are always bracketed, as in Miranda.  
  * Match expressions are parsed with the offside rule: the components can't start left of `match`, and the patterns and right-hand-side expressions have to be right of `+`. (Explicit match expressions will one day disappear, I hope, in favour of Miranda-style matching on function parameters.)  
  * Function applications are *E* *E* -- juxtaposition. And of course left associative, so that *E* *E* *E* is (*E* *E*) *E*.  There's a function library (see below) and perhaps one day there will be downloadable bundles of functions.  
  * Absolutely no process stuff, no manipulation of qubits. But see *print_string*, *print_strings* and *print_qubit* below.  

 * Operators  
    
    * `@` is list append.  
    * `::` is list cons.  
    * arithmetic operators *aop* -- see below.  
    * `<`, `<=`, `=`, `<>`, `>=`, `>` comparison operators *cop*. `=` handles anything which is an equality type (no qubits, qstates, functions, processes, channels). Operands of the inequality operators must be numbers.
    * `&&`, `||`, boolean operators *bop*.
    
* Arithmetic operators
  
  We have the normal operators for unary negation (`-`), addition (`+`), subtraction (`-`), multiplication (`*`) and exponentiation (`**`), as well as tensor product (`&otimes;` or `><`) and tensor exponentiation (`&otimes&otimes` or `><><`).  Numerical exponentiation's second argument must be a whole number (run-time check).
  
  Arithmetic operators are heavily overloaded, and to make typechecking work it is sometimes necessary to explicitly type some variables. These are the types currently understood:
  
  * unary negation: 
    + `num` &rarr; `num`
    + `sxnum` &rarr; `sxnum`
  * addition and subtraction: 
    + `num` &rarr; `num` &rarr; `num` 
    + `sxnum` &rarr; `sxnum` &rarr; `sxnum` 
    + `matrix` &rarr; `matrix` &rarr; `matrix`
  * multiplication:
    + `num` &rarr; `num` &rarr; `num` 
    + `sxnum` &rarr; `sxnum` &rarr; `sxnum` 
    + `matrix` &rarr; `matrix` &rarr; `matrix` 
    + `gate` &rarr; `gate` &rarr; `gate` 
    + `gate` &rarr; `ket` &rarr; `ket` 
    + `ket` &rarr; `bra` &rarr; `matrix` 
    + `bra` &rarr; `ket` &rarr; `sxnum` 
    + `sxnum` &rarr; `matrix` &rarr; `matrix` 
    + `matrix` &rarr; `sxnum` &rarr; `matrix` 
  * exponentiation:
    + `num` &rarr; `num` &rarr; `num` 
  * tensor product:
    + `matrix` &rarr; `matrix` &rarr; `matrix` 
    + `bra` &rarr; `bra` &rarr; `bra` 
    + `ket` &rarr; `ket` &rarr; `ket` 
    + `gate` &rarr; `gate` &rarr; `gate` 
  * tensor exponentiation
    + `matrix` &rarr; `num` &rarr; `matrix`  
    + `bra` &rarr; `num` &rarr; `bra`  
    + `ket` &rarr; `num` &rarr; `ket`  
    + `gate` &rarr; `num` &rarr; `gate`  
 
* Process name *N*

  Starts with an upper-case letter, continues with alphanumeric, prime and underscore.
  
* Variable name *x*

  Starts with a lower-case letter, continues with alphanumeric, prime and underscore. (Actually, it seems, you can get away with upper case, but names in function definitions have to start with lower case.)

  
## Input-Output channels, *show* and *qval*

There's an input channel *in*

  * *in*: ^*string*
  
It reads a single line of input as a string. Writing to it is a run-time error, because I don't know how to typecheck receive-only channels.

There are functions which print out strings and *qstates*. But it's inelegant to use them in a process. So there are output channels.

  * *out*: ^*[string]*
  * *outq*: ^*qstate*

outq is peculiar for peculiar reasons. It allows logging of a qubit's state. But it couldn't be a channel which takes a qubit, because if you send a qubit down a channel, you lose it. So there's a special type *qstate*, the result type of *qval*: *qubit* &rarr; *qstate*, which is a classical value that can be sent down the *outq* channel. To ensure no computational cheating, there's nothing else you can do with a *qstate* value. 

Reading from an output channel is a runtime error, because I don't know how to typecheck send-only channels.

To help with output, there is the special function *show*, as in Miranda

  * *show*: '\**a* &rarr; *string*
  
-- it takes any value and turns it into a string. It produces `"<qubit>"` for a qubit, `"<qstate>"` for a qstate, to stop computational cheating. It treats functions, processes and channels similarly opaquely, but for different reasons.

For qubits there is *qval*

  * *qval*: *qubit* &rarr; *qstate*

The use of *qval* is connected to the *outq* channel: *outq*!(*qval* *q*) prints a string `#`*q*`:`*V*, the qubit's index *q* and a representation *V* of its state as a symbolic-number vector in the computational basis -- including, if there is entanglement, a list of the indices of the qubits it's entangled with.

## Symbolic calculation

Qtpi uses a symbolic quantum calculator: only during quantum measurement does it calculate numerically. This enables it to do some nice tricks, like accurately 'teleporting' a qubit whose value is unknown. It also means that it can do exact calculations, though it has to approximate when calculating measurement probabilities.

Qubits are represented as integer indices into a quantum state of unitary vectors in the computational basis defined by `|0>` and `|1>`. An unentangled qubit indexes a pair of complex-valued amplitude expressions (*A*, *B*) representing (*A*`|0>`+*B*`|1>`); either *A* or *B* may be zero, and always |*A*|<sup>2</sup>+|*B*|<sup>2</sup>=1. A simply-entangled pair of qubits indexes a quadruple (*A*,*B*,*C*,*D*), representing \[`#`*i*; `#`*j*\](*A*`|00>`+*B*`|01>`+*C*`|10>`+*D*`|11>`), where *i* and *j* are the indices of the entangled qubits (again, some of *A*, *B*, *C* and *D* may be zero). And so on for larger entanglements: famously, *n* qubits need 2<sup>*n*</sup> amplitudes.

The constant `h` is *sqrt*(1/2), and `h(`*k*`)` means `h`<sup>*k*</sup>.  *h* is also *cos*(&pi;/4) and *sin*(&pi;/4). The constant `f` is *sqrt*((1+`h`)/2), which is *cos*(&pi;/8), and `g` is *sqrt*((1-`h`)/2), which is *sin*(&pi;/8).

An unknown qubit with index *k* starts life as the vector (`a`<sub>k</sub>`|0>`+`b`<sub>k</sub>`|1>`), and the evaluator knows that |`a`<sub>k</sub>|<sup>2</sup>+|`b`<sub>k</sub>|<sup>2</sup>=1. To enhance the randomness of the execution, there are secret real values attached to `a`<sub>k</sub> and `b`<sub>k</sub>, used when the qubit (or a qubit with which is entangled) is measured. In computing |`a`<sub>k</sub>|<sup>2</sup> or |`b`<sub>k</sub>|<sup>2</sup> qtpi uses the fact that |*x*|<sup>2</sup> = *x* * <span style="text-decoration:overline;">*x*</span>, which is *x* times its complex conjugate <span style="text-decoration:overline;">*x*</span>. 

### Modulus

In principle a vector's amplitudes should be such that |*A*|<sup>2</sup>+|*B*|<sup>2</sup> = 1 for an unentangled qubit, or |*A*|<sup>2</sup>+|*B*|<sup>2</sup>+|*C*|<sup>2</sup>+|*D*|<sup>2</sup> = 1 for a pair of entangled qubits, and so on. But when the amplitude formulae are very complicated it can sometimes be difficult for qtpi's calculator to normalise the result of a calculation (typically this happens with a large entanglement when one of the qubits is measured). So probability vectors also carry a probability-amplitude modulus, the sum of the squares of its amplitudes. Normally this is 1, and not mentioned, but when it is not 1, the vector is printed prefixed by `<<`*M*`>>`, where *M* is the modulus formula. The interpretation is that every amplitude in the vector is divided by &radic;<span style="text-decoration:overline;">*M*</span>.  

The modulus is taken into account numerically during measurement.

### Complex probabilities

Probability amplitudes always represent complex numbers *x*+*iy*, but often *y* is zero. 

## Gates *gate*

The built-in library defines various named gates (for meaning of `f`, `g` and `h`, see above). Mostly arity 1, except `Cnot` which is arity 2, `F` and `T`, which are arity 3.

  * `H`: the Hadamard gate, takes `|0>` to `h|0>+h|1>`, `|1>` to `h|0>-h|1>`. A kind of 45&deg; rotation (&pi;/4).
  * `I`: takes `|0>` to `|0>`, `|1>` to `|1>`. Identity.
  * `X`: takes `|0>` to `|1>`, `|1>` to `|0>`. Exchange, inversion, not.
  * `Z`: takes `|0>` to `-|1>`, `|1>` to `|0>`. (dunno what to call it.)
  * `Y`: takes `|0>` to `-`*i*`|1>`, `|1>` to *i*`|0>`. (In some descriptions, `Y` is equivalent to the product `Z*X`. Qtpi has the Pauli version.)
  * `Cnot`: takes `|00>` to `|00>`, `|01>` to `|01>`, `|10>` to `|11>`, `|11>` to `|10>`. (Controlled-not). Also known as `CNot` and `CNOT`.
  
  * `Rz`: takes `|0>` to `f|0>+g|1>`, `|1>` to `-g|0>+f|1>`. A kind of 22.5&deg; rotation (&pi;/8).
  * `Rx`: takes `|0>` to `|0>`, `|1>` to `(f+ig)|1>`. A kind of 22.5&deg; phase rotation (&pi;/8).
  
  * `F`: the Fredkin gate, takes `|101>` to `|110>` and vice-versa. Also known as `Cswap`, `CSwap` and `CSWAP`.
  * `T`: the Toffoli gate, takes `|110>` to `|111>` and vice-versa. (Controlled-controlled-not).
  
There's a built-in function *phi: num &rarr; gate*:

  * `phi 0` is `I`; `phi 1` is `X`; `phi 2` is `Z`; `phi 3` is `Y`.
  
There are lots more well-known gates -- e.g. 'square root of NOT' -- which aren't included. 

## The *dispose* channel

Qubits get discarded: Alice sends one to Bob, Bob receives it, measures it, remembers the result, and then waits for the next one. The qubit is destroyed on detection (unless you use the switch '`-measuredestroys false`'), and it vanishes from the simulation. A vanished qubit is in fact recycled.

Qubits that aren't measured, and even measured qubits if `-measuredestroys false` is used, live for ever. Sometimes this is inconvenient (it muddies the waters if you are debugging, for example). To solve this problem there is a *dispose* channel for qubits: send a qubit down the *dispose* channel and it vanishes. It will be made available to be recycled, unless it is entangled, in which case it may be made available later if the entanglement collapses, or it is an unknown, in which case it will be forever in limbo. Like any sent-away qubit, you can't use it once it's disposed (see [the resourcing document](https://github.com/mdxtoc/qtpi/blob/master/docs/ownership.md/) for explanation).

Reading from from the *dispose* channel is a run-time error, because I don't know how to typecheck send-only channels.

<a name="restrictions"></a>

## Restrictions

In protocols, and in quantum computing in general, qubits are fragile things. They are sent through gates, transmitted through channels, measured. Protocol descriptions (e.g. QKD) talk of processes sending qubits on a quantum channel and separately communicating information like basis and value over classical channels. So although as a programmer you might expect to be able to make lists of qubits, tuples of qubits and the like, for simplicity of description of protocols I impose restrictions which means that anything other than single qubits are useless. This also massively simplifies *resourcing*: see [the resourcing document](https://github.com/mdxtoc/qtpi/blob/master/docs/ownership.md/) for explanation of how hard it is otherwise.

These restrictions give you a language in which qubits are known only by a single name at any time. This simplifies the description of protocols, I believe, and it simplifies resource-checking, but it's also there for aesthetic reasons.

It is impossible to branch according to the state or identity of a qubit unless you measure it first. (In unsimulated real life you couldn't ...). Likewise on the identity or equality of a function or a process.

  * **A channel is either `^qubit` or `^classical`**.
    	
  * **A process argument is either `qubit`, or classical**.
  
  	Note that a channel is a classical value, whatever its type. So is a function or a process. (Process types exist, but currently process values can't be manipulated.)
  
  * **No qubit-valued conditionals as  process argument or send argument**.
  
  	Conditionals include `if` and pattern-matching. It's ok to have qubit-valued conditionals in other positions, such as
  	
  			if a=0 then q1 else q2 fi >> H

  * **`let` and pattern-matching can only bind classical values**.
  
  	This is a surprising restriction, because I included pattern matching in qtpi precisely to make it safe to bind qubits, and I believe the resource-checker could be made to cope with it. But I think it's a better language without it.
    
  * **A function takes classical arguments and delivers a classical result**.
  * **A function cannot refer to a free qubit**.
  
  	Without the result restriction resource-checking simply wouldn't work. Without the argument and free-variable restrictions some computational cheating could occur: e.g. a process could get the qstate of another process's qubit.
  	
  	There is a deliberate loophole: this restriction is applied to function *definitions*. This is to allow library functions to take non-classical arguments, and so far this applies only to `qval` and `show`. But be careful with it: see below.

  * **No comparison of qubits, qstates, or values containing qubits or qstates**.
  
  	This stops programs doing anything, apart from quantum measurement, to exploit the value or identity of a qubit.
  
  * **No comparison of functions, processes or channels, or values containing functions, processes or channels**.
  
  	Restriction on function comparison is standard in functional programming. You can't compare function values, because they are infinite. Ditto processes (which may one day arise as computational values: they are already a type). Channel comparison seems dodgy too, so I prohibit it.
  
  * **Library functions don't expose simulation state**.
  
  	There used to be a function *qubit_state* which gave you a string representation of a qubit's internal state. Useful for diagnostic printing, I thought. Then I realised it allowed the program to branch on whether a pair of qubits are entangled or not, by comparing the results of *qubit_state* on them. Horror!
  	
  	Not all is lost: there's *qval* which gives a *qstate*, there's the *outq* channel which accepts a *qstate*, and the `-verbose qsim` switch on Qtpi allows you to watch the simulation in detail.
  	
  	Since qtpi is in the public domain, you can modify `library.ml` to define new library functions. If you define one with a non-classical parameter, please make it the *last* parameter and don't deliver a functional result. This is to stop partial application baking-in access to qubits.
  	
  	This is a restriction on the implementation of the language. Not sure how to police it ... especially if I allow downloadable libraries. Hmm.
  	
## Interface functions

We need to be able to read and write stuff: reading to give instructions like how many qubits to create; writing to describe results. It's also useful to include some functions to deal with lists and tuples. 

The library is mostly inspired by Miranda and Bird & Wadler's "Introduction to Functional Programming". Easy to add more (see the file library.ml). 

Most of these functions deal in classical values only (*'a* rather than *'\*a*). But none (except for the absurd case of *abandon*) returns a value of a non-classical type.
    
Following the introduction of the *num* type in place of the old *int*, we can have fractional numbers. But several of the library functions insist on non-fractional arguments: *bitand*, *drop*, *nth*, *num2bits*, *randbits*, *tabulate*, *take*. If this causes a problem, use *floor*, which converts fractions to integers.

  * *abandon*: *[string]* &rarr; *'\*a*  
	* stops the program and doesn't return. For typechecking purposes 'returns' a value which might be any type. 
  * *append*: *['a]* &rarr; *['a]* &rarr; *['a]*
  * *compare*: *''a* &rarr; *''a* &rarr; *num*
	* 0 for equal, -1 for *a*\<*b*, 1 for *a*>*b* (as C/OCaml)
  * *concat*: *[['a]]* &rarr; *['a]*
  * *const*: *'a* &rarr; *'b* &rarr; *'a*
  * *degate*: *gate* &rarr; *matrix*
  * *drop*: *num* &rarr; *['a]* &rarr; *['a]*
  * *dropwhile*: (*'a* &rarr; *bool*) &rarr; *['a]* &rarr; *['a]*
  * *engate*: *matrix* &rarr; *gate* (checks matrix is square and unitary)
  * *exists*: (*'a* &rarr; *bool*) &rarr; *['a]* &rarr; *bool*
  * *filter*: (*'a* &rarr; *bool*) &rarr; *['a]* &rarr; *['a]*
  * *floor*: *num* &rarr; *num*
  * *foldl*: (*'a* &rarr; *'b* &rarr; *'a*) &rarr; *'a* &rarr; *['b]* &rarr; *'a*
  * *foldr*: (*'a* &rarr; *'b* &rarr; *'b*) &rarr; *'b* &rarr; *['a]* &rarr; *'b*
  * *forall*: (*'a* &rarr; *bool*) &rarr; *['a]* &rarr; *['a]*
  * *fst*: (*'a*, *'b*) &rarr; *'a*  
  * *hd*: *['a]* &rarr; *'a*  
	  * raises an exception if applied to `[]`  
  * *iter*: (*'a* &rarr; *'b*) &rarr; *['a]* &rarr; *unit*
  * *length*: *['a]* &rarr; *num*  	
  * *map*: (*'a* &rarr; *'b*) &rarr; *['a]* &rarr; *['b]*
  * *max*: *num* &rarr; *num* &rarr; *num*
  * *min*: *num* &rarr; *num* &rarr; *num*
  * *nth*: *['a]* &rarr; *num* &rarr; *'a*
  * *phi*: *num* &rarr; *gate*
      * see 'Gates' above.
  * *qval*: *qubit* &rarr; *qstate*
  * *randbit*: *unit* &rarr; *bit*
  * *randbits*: *num* &rarr; *[bit]*
  * *rev*: *['a]* &rarr; *['a]*
  * *show*: *'\*a* &rarr; *string*
	  * converts a value to a string. Gives a deliberately opaque result if applied to a qubit, function, process, channel or qstate.  
  * *sort*: (*''a* &rarr; *''a* &rarr; *num*) &rarr; *'['a]* &rarr; *'['a]*
	  * sorts according to order defined by first argument -- 0 for equal, -1 for *a*\<*b*, 1 for *a*>*b* (as C/OCaml)
  * *snd*: (*'a*, *'b*) &rarr; *'b*  
  * *tabulate*: *num* &rarr; (*num* &rarr; *'a*) &rarr; *['a]*
  * *tabulate_m*: *num* &rarr; *num* &rarr; (*num* &rarr; *num* &rarr; *sxnum*) &rarr; *matrix*
  * *tabulate_diag_m*: *num* &rarr; (*num* &rarr; *sxnum*) &rarr; *matrix*
  * *take*: *num* &rarr; *['a]* &rarr; *['a]*
  * *takewhile*: (*'a* &rarr; *bool*) &rarr; *['a]* &rarr; *['a]*
  * *tl*: *['a]* &rarr; *['a]*  
	  * raises an exception if applied to `[]`  
  * *unzip*: [(*'a*,*'b*)] &rarr; ([*'a*], [*'b*])
  * *zip*: [*'a*] &rarr; [*'b*] &rarr; [(*'a*,*'b*)]
	  * raises an exception if applied to lists of differing lengths (but probably shouldn't)
  * 
  * *bitand*: *num* &rarr; *num* &rarr; *num*
  * *bits2num*: *[bit]* &rarr; *num*
  * *num2bits*: *num* &rarr; *[bit]*
  * 
  * *read_alternative*: *string* &rarr; *string* &rarr; [(*string*,*'a*)] &rarr; *'a*
	  * *read_alternative* *prompt* "/" [(*s0*,*v0*);(*s1*,*v1*);...] prints *prompt*(*s0*/*s1*/...) and returns *v0* or *v1* or ... according to what the user inputs
  * *read_bool*: *string* &rarr; *string* &rarr; *string* &rarr; *bool*
	  * prompt, true\_response, false\_response
  * *read_num*: *string* &rarr; *num*
  * *read_string*: *string* &rarr; *string*
	  * *read_int* and *read_string* take a prompt-string argument.  
  * 
  * *print_qubit*: *qubit* &rarr; *unit*
	  * *print_qubit* *q* has the same effect as *outq*!(*qval* *q*)
  * *print_string*: *string* &rarr; *unit*
	* *print_string* *E* has the same effect as *out*!\[*E*\]
  * *print_strings*: *[string]* &rarr; *unit*
	* *print_strings* *Es* has the same effect as *out*!*Es*
