This directory contains tests for the typechecker.

Follow these guidelines:

* Tests in a file not ending with _failN.erl (where N is empty or some natural number)
  are expected to pass the type checker.
* Non-failing tests should contain a simple unit test to make sure that the code
  does what you think it does.
* A function whose name ends with _infer is treated in two ways: (a) the function
  is checked against the type given in then spec (as usual). (b) type type of the function
  is inferred and then the inferred type is tested to be equivalent to the type in the spec.
  (The latter is a special mode of the type checker.)
* Tests in a file ending with _failN.erl (where N is empty or some natural
  number) are expected to fail the type checker.
