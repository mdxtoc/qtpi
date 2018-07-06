# qtpi syntax

Based on CQP (Gay & Nagarajan, POPL 2005) and therefore on the pi calculus. Some changes cosmetic (e.g. fewer square brackets, fewer capital letters); some for convenience (no mandatory types, because there's a typechecker); some because I don't like hiding state-changing operations inside expressions (e.g. unary gates, measurement); some to be closer to the pi calculus; new operators intended to be easy to read. Others noted elsewhere.

## Grammar 

Processes *P*, steps *S*, expressions *E*, types *T*, etc. Sorry about layout (knocking this up in Markdown). Square brackets surround optional elements.

* Process *P*  
| *S* ``.`` *P*   
| ``(`` *P* ``|`` ... ``|`` *P* ``)``  
| ``if`` *E* ``then`` P ``else`` P ``fi``  
| ``(new`` *x* [ ``:`` *T* ] ``,``  ... ``,`` *x* [ ``:`` *T* ] ``)`` *P*   
| ``(newq`` *x* [ ``=`` *V* ] ``,``  ... ``,`` *x* [ ``=`` *V* ] ``)`` *P*  
| *x* ``(`` *E*  ``,``  ... ``,`` *E*  ``)``  
| ``_0``

  Type specs in '``new``' are optional (and you can optionally write ``: qbit`` after the names in a ``newq`` binding -- but why would you bother?).  
  Initialisation to basis vectors in ``new``  is also optional.  
  The process name '*x*' in a process call *x* ``(`` *E*  ``,``  ... ``,`` *E*  ``)`` must start with a capital letter.  
  '``_0``' is the null process.
  
* Step *S*  
| *E* ``?`` ``(`` x [ ``:`` *T* ] ``,``  ... ``,`` *x* [ ``:`` *T* ] ``)``    
| *E* ``!`` *E* ``,``  ... ``,`` *E*   
| *E*  ``,``  ... ``,`` *E* ``>>`` *G*   
| *E* ``??`` *G*    

  '``?``' is read, as in the pi calculus: the first *E* must be a channel; the bindings are bracketed, as in the pi calculus; the types are optional.  
  '``!``' is write, as in the pi calculus: the first *E* must be a channel; the output tuple can be bracketed if you wish.  
  '``>>``' is 'send through a gate'; the *E*s must be qbits.  
  '``??``' is measure; *E* must be a qbit.
  
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
  '``->``' separates elements of a function type.   
  Type variables ``'``*x* are used in function types, as in ML, OCaml, Miranda, Haskell etc.; function types are needed in '``given``  clauses (see below).



