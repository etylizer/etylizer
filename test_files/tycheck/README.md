This directory contains tests for the typechecker.

The driver for running the tests is test/tycheck_tests.erl

Files in this directory should follow some conventions:

* A test that should fail is either placed in a file ending with _failN.erl
  (where N is empty or some natural number) or its first line is `% Error`.
  * If the first line of the file starts with `% ERROR`, then all following comment
    lines are treated as a string that must occur somewhere in the error message. The first
    space character after the `%` is ignored.
* If the first line of a file is `% SKIP`, then the test is skipped.
* Otherwise, the file must typecheck successfully.
  * Non-failing tests should contain a simple unit test to make sure that the code
    does what you think it does.

The following behavior is not supported yet:

* A function whose name ends with _infer is treated in two ways: (a) the function
  is checked against the type given in then spec (as usual). (b) type type of the function
  is inferred and then the inferred type is tested to be equivalent to the type in the spec.
  (The latter is a special mode of the type checker.)
