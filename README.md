# smt4Inductive_Invariants
Searching for the inductive invariants by the SMT method.

Convert murphi code to python semantics and construct f(guard, assignment', assumption, !inv', inv) in python semantics, then call z3 to solve f to obtain counterexamples and auxiliary invariants. The final obtained protocol and invariants are converted to ivy format, and ivy is used to check whether the correct inductive invariants are found.
