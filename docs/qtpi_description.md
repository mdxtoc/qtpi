# qtpi language description

Based on CQP (Gay & Nagarajan, POPL 2005) and therefore on the pi calculus. Some changes cosmetic (e.g. fewer square brackets, fewer capital letters); some for convenience (no mandatory types, because there's a typechecker); some because I don't like hiding state-changing operations inside expressions (e.g. unary gates, measurement); some to be closer to the pi calculus; new operators intended to be easy to read. 

## Grammar 

Processes *P*, steps *S*, expressions *E*, types *T*, process names *N*, variable names *x*, parameters *par*, basis vectors *V*. Sorry about layout (knocking this up in Markdown). Square brackets surround optional elements.

* Process *P* 

  | *S* ``.`` *P*   
  |  *P* ``|`` ... ``|`` *P*   
  | ``if`` *E* ``then`` *P* ``else`` *P* ``fi``  
  | ``(new`` *par*  ``,``  ... ``,`` *par* ``)`` *P*   
  | ``(newq`` *par* [ ``=`` *V* ] ``,``  ... ``,`` *par* [ ``=`` *V* ] ``)`` *P*  
  | *N* ``(`` *E*  ``,``  ... ``,`` *E*  ``)``  
  | ``_0``  
  | ``(`` *P* ``)``  

  The parameters in ``new`` must describe channels.    
  The parameters in  ``newq`` must describe qbits. Initialisation to basis vectors is optional (and then you get (a|0>+b|1>), for unknown a and b).  
  '``_0``' is the null process (termination).
  
* Parameter *par*

  | *x* [ ``:`` *T* ]
  
  Parameter type specs are optional, always.
  
* Step *S*  

  | *E* ``?`` ``(`` x [ ``:`` *T* ] ``,``  ... ``,`` *x* [ ``:`` *T* ] ``)``    
  | *E* ``!`` *E* ``,``  ... ``,`` *E*   
  | *E*  ``,``  ... ``,`` *E* ``>>`` *G*   
  | *E* ``??`` *G*    

  '``?``' is read, as in the pi calculus: the first *E* must be a channel; the bindings are bracketed, as in the pi calculus; the types are optional.  
  '``!``' is write, as in the pi calculus: the first *E* must be a channel; the output tuple can be bracketed if you wish.  
  '``>>``' is 'send through a gate'; the *E*s must describe single qbits. The arity of the input tuple must match the gate (e.g. _H gets one qbit, _Cnot gets 2). (CQP had ``*=``, which looks like an assignment.)  
  '``??``' is measure; *E* must describe a single qbit.
  
  The ``{`` *E* ``}`` step of CQP is not included (reasons of taste, mostly).
  
* Type *T* 

  | ``int``  
  | ``bool``  
  | ``bit``  
  | ``unit``  
  | ``qbit``  
  | ``'``*x*  
  | *T* ``list``  
  | *T* ``*`` ... ``*`` *T*  
  | ``^`` *T*  
  | *T* ``->`` ... ``->`` *T*  
  | *T* ``process``  
  | ``(`` *T* ``)``  

  '``*``' separates elements of a tuple type.   
  Type variables ``'``*x*, function types *T* ``->`` ... ``->`` *T* and process types *T* ``process`` are used in the ``given`` clause (see program description below).  
  The syntactic precedence of types is more or less as listed, or so I hope and intend. 

  
  Explicit types are optional syntactically, as in ML and OCaml and Miranda and Haskell and all good strongly-typed languages. The typechecker infers them.

* Expression *E*

  The ususal stuff: constants (``0b1`` and ``1b1`` are bit constants), variables, arithmetic (not much implemented yet), comparison (only '=' and '!=' implemented so far), boolean operations (only && and || so far).
  
  Conditionals are ``if`` *E* ``then`` E ``else`` E ``fi``. 
  Function calls are *E* *E* -- juxtaposition. And of course left associative, so that *E* *E* *E* is (*E* *E*) *E*.  
  
  No process stuff, no steps.  
  
* Basis vectors *V*

  |0>, |1>, |+> and |->. Used only when creating a new qbit.  

* Process name *N*

  Starts with an upper-case letter, continues with alphanumeric, prime and underscore.
  
* Variable name *x*

  Starts with a lower-case letter, continues with alphanumeric, prime and underscore.

## Program description

A program is an optional ``given`` list and then a bunch of process definitions. One of the process descriptions must be ``System``, which can have only integer, boolean or no parameters ('unit' type).

* Process definition *D*

  | *D* ``(``  *par*  ``,``  ... ``,`` *par* ``)`` = *P*
  
  Pragmatically it seems to be a good idea to include typespecs in process definition parameters.
  
  None of the parameters can be a process type.
  
* ``given`` list

	The word ``given``, followed by a comma-separated list of process and function names, describing things that aren't defined in the program.
	
	The process parameters allow 'stuck' processes like 'Win', 'Lose' and so on, which help you to work out how the system finishes.
	
	The function parameters are there because it is necessary to use hd, tl, etc. when manipulating lists, and lists seem essential. I didn't want to build all that stuff in (because where do I stop?) so I imagined I could build an interface. I still imagine, but haven't done it yet.
	
	You are allowed type variables in the function types. Of _course_ you need them!
	