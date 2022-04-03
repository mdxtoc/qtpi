* *logging*

  | *label* `:` *loggingprocess*  
  | *label* `:` *loggingprocess* *logging*  

* *loggingprocess*
  
  A sub-process which may not include process invocations, parallel sub-processes or input commands. It may include output commands, but cannot send qubits. It can only be called once from the main process text, and can refer to any names visible at the point of call.

* *label*

  A sequence of digits. Identifies a logging process.

## Logging and testpoints

Protocol descriptions become harder to read if they include lots of output commands. Often the output commands -- logging commands, in effect -- take up more space than the protocol description. It's possible to separate logging from protocol description.

A process may end `with` *logging*, where *logging* is a sequence of labelled subprocesses (see *logging* above); those subprocesses can only make output steps sending classical values. In the body of the process itself there may be testpoints `/^` *label*, indicating that a particular logging subprocess should run at this point.

If the logging subprocesses use parameters which aren't required in the body of the process, it may end `with` `(` *par* `,` ... `,` *par* `)` *logging*; the additional parameters are only available in the logging subprocesses. When the process is called, the caller must provide the normal and the additional logging parameters.

If a process wants to use the logging parameters in the arguments of a process call (e.g. in a recursive call) then it may do so by adding `/^` `(` *E* `,` ... `,` *E* `)` to the arguments of the call; those extra arguments can refer to the logging parameters.

