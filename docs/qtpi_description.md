# qtpi language description

Based on CQP (Gay & Nagarajan, POPL 2005) and therefore on the pi calculus. Some changes cosmetic (e.g. fewer square brackets, fewer capital letters); some for convenience (no mandatory types, because there's a typechecker); some because I don't like hiding state-changing operations inside expressions (e.g. unary gates, measurement); some to be closer to the pi calculus; new operators intended to be easy to read. 

## Grammar 

Processes *P*, input-output steps *IO*, quantum steps *Q*, expressions *E*, types *T*, process names *N*, variable names *x*, parameters *par*, patterns *pat*, gate expressions *G*. Sorry about layout (knocking this up in Markdown). Square brackets surround optional elements.

* Process *P* 

  | *Q* `.` *P*  
  | *IO* `.` *P* `<+>` ... `<+>` *IO* `.` *P*   
  | *P* `|` ... `|` *P*   
  | `if` *E* `then` *P* `else` *P* `fi`  
  | `match` *E* `.` *pat* `.` *P* `<m>` ... `<m>` *pat* `.` *P* `hctam`  
  | `( new` *par*  `,`  ... `,` *par* `)` *P*   
  | `( newq` *par* [ `=` *E* ] `,`  ... `,` *par* [ `=` *E* ] `)` *P*  
  | `( let` *pat* = *E* `)` *P*  
  | `{` *E* `}` `.` *P*  
  | *N* `(` *E*  `,`  ... `,` *E*  `)`  
  | `(` *P* `)`  
  | `_0`

  * `new` creates channels.    
  * `newq` creates qbits. Initialisation to basis vectors is optional (without it you get (*a*`|0>`+*b*`|1>`), for unknown *a* and *b*, where *a*<sup>2</sup>+*b*<sup>2</sup>=1.  
  * The guarded sum *IO* `.` *P* `<+>` ... `<+>` *IO* `.` *P* is not yet supported: single input-output steps only at present. It uses the separator `<+>` instead of `+` to avoid parsing problems.  
  * match processes also use an <m> separator, to avoid parsing problems. I would have preferred `<+>`, or indeed `+`, if I could have made it work.  
  * `_0` is the null process (i.e. termination). I would have used `()` (null parallel or null guarded sum: same difference) but it would have caused parsing problems.  
  * You can execute an arbitrary expression via a 'let' binding, if you wish.  Sorry.
  
* Quantum step *Q*
  
  | *E* `,` *E* `,` ... `,` *E* `>>` *G*    
  | *E* `=?` (*par*)    

  * '`>>`' is 'send through a gate'; each left-hand *E* must describe a single qbit. The arity of the input tuple must match the arity of the gate (e.g. _H takes one qbit, _Cnot takes 2, _Fredkin if we had it would take 3, and so on).  
  * `=?` is measure, in the computational basis defined by `|0>` and `|1>`.  The parameter *par* binds the single-bit result. 
  * I should probably add `=H?` for measuring in the Hadamard basis.  
  * CQP had `*=` for measure, which looked like an assignment, so I changed it to `??`.   

* Input-output step *IO*  

  | *E* `?` `(` *par* `,`  ... `,` *par* `)`    
  | *E* `!` *E* `,`  ... `,` *E*   

  * '`?`' is read, as in the pi calculus: the first *E* must be a channel; the bindings are bracketed, as in the pi calculus; the types are optional.  
  * '`!`' is write, as in the pi calculus: the first *E* must be a channel; the output tuple can be bracketed if you wish.  
  * Channels each carry either a qbit or a classical value (not including any qbits).  
  
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

  * `basisv` is the type of basis vectors (see below).  
  * '`*`' separates elements of a tuple type.   
  * Type variables `'`*x* and function types *T* `->` ... `->` *T* are currently for internal use.  
  * Process types *T* `process` are used in the `given` clause (see program description below).  
  * The syntactic precedence of types is more or less as listed, or so I hope and intend. 
  * Explicit types are optional syntactically, as in ML and OCaml and Miranda and Haskell and all good strongly-typed languages. The typechecker infers them. It's probably pragmatic to include them in the parameter list of a process definition, and in '`new`' channel declarations.

* Pattern *pat*

  | `_`  
  | ` []`  
  | `()`  
  | *constant*  
  | *x*  
  | *x* : *type*  
  | *pat* `::` *pat*  
  | *pat* `,` ... `,` *pat*  
  | `(` *pat* `)`  


* Expression *E*

  * The ususal stuff: constants (`0b1` and `1b1` are bit constants; `|0>`, `|1>`, `|+>` and `|->` are basis vectors), variables, arithmetic (not much implemented yet), comparison, boolean operations (only && and || so far).
  
  * Conditionals are `if` *E* `then` *E* `else` *E* `fi`. 
  
  * Match expressions are `match` *E* `.` *pat* `.` *E* `<m>` ... `<m>` *pat* `.` *E* `hctam`.  
  
  * Function calls are *E* *E* -- juxtaposition. And of course left associative, so that *E* *E* *E* is (*E* *E*) *E*.  There's a function library (see below) and Real Soon Now there will be downloadable bundles of functions.  
  
  * No process stuff, no steps.  
  
* Built-in operators  
    
    * `@` (append) was an operator in one of Gay & Nagarajan's examples.  
    * `::` (cons) is now included.  
    * `++` combines bits: *a*`++`*b* is *a* times 2 plus *b*. Included because it helps with range typing.

* Process name *N*

  Starts with an upper-case letter, continues with alphanumeric, prime and underscore.
  
* Variable name *x*

  Starts with a lower-case letter, continues with alphanumeric, prime and underscore.

## Program description

A program is an optional `given` list and then a bunch of process definitions. One of the process descriptions must be `System`, which must have no parameters ('unit process' type).

* Process definition

  | *N* `(`  *par*  `,`  ... `,` *par* `)` = *P*
  
  * Types are optional, but it seems to be pragmatic to include them.
  * None of the parameters can be a process type.
  
* `given` list

	| `given` *N* `:` *T* `,` *N* `:` *T* `,` ... *N* `:` *T*  

    * Gives names and types of processes that aren't defined in the program. This allows undefined processes like 'Win', 'Lose' and so on, which help you to work out how the system finishes from a print-out of the final state. (Now I have a library which includes output functions, this seems like an idea that could be dropped.)
    
* Interface functions

    We need to be able to read and write stuff: reading to give initial values like how many qbits to create; writing to describe results. It's also useful to include some functions to deal with lists and tuples. 
    
    **But**, *but*, but. Functions can't deliver qbits or values containing qbits. See the documentation on resourcing for an explanation.
    
    Here are the functions I currently provide. Easy to add more (see the file library.ml) 
    
    * *length*: *'a list* -> *int*  	
    * *hd*: *'a list* -> *'a*  	(raises an error if applied to `[]`) 
	* *tl*: *'a list* -> *'a list*  	(raises an error if applied to `[]`)  
	* *rev*: *'a list* -> *'a list*
	* *append*: *'a list* -> *'a list* -> *'a list*
	* *iter*: (*'a* -> *'b*) -> *'a list* -> *unit*
	* *map*: (*'a* -> *'b*) -> *'a list* -> *'b list*
	* *take*: *int* -> *'a list* -> *'a list*
	* *drop*: *int* -> *'a list* -> *'a list*
	* *fst*: *'a*\**'b* -> *'a*  
	* *snd*: *'a*\**'b* -> *'b*  
	
	* *read_int*: *string* -> *int*  
	* *read_string*: *string* -> *string*  

	* *abandon*: *string* -> *'a*  

	* *qbit_state*: *qbit* -> *string*  

	* *print_string*: *string* -> *unit*  
	* *print_strings*: *string list* -> *unit* 
	* *string_of_value*: *'a* -> *string*
	
	 *hd*, *tl*, *fst* and *snd* do what you'd expect (but you can't use them to deliver qbits: see above).  
	*read_int* and *read_string* take a prompt-string argument.  
	*abandon* stops the program and doesn't return (i.e. raises an exception).  
	
	*qbit_state* gives you a string *q*`:(`*A*`|0>`+*B*`|1>)`, the qbit's index *q* and a representation of its state as a probability vector. In probabilities the constant `h` means *sqrt*(1/2), and `h(`*k*`)` means (*sqrt*(1/2))<sup>*k*</sup>. If *q* is entangled with *q'* you will see stuff like *q*`:[`*q*;*q'*`](`*A*`|00>`+*B*`|01>+`*C*`|10>`+*D*`|11>)`. The standard example would be `0:[0,1](h|00>+h|01>)`. And so on for larger entanglements.
