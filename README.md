ALIVe: Automatic LLVM's Instcombine Verifier
============================================

ALIVe is a tool that can prove the correctness of InstCombine optimizations
specified in a high-level language.

WARNING: This tool is not complete and its results should not be relied upon.


Requirements
------------
ALIVe requires Z3Py, which can be obtained from http://z3.codeplex.com
You should use the 'unstable' branch of Z3, with a checkout at least as recent
as 25/Jun/2014 (7158e814d1dc22eabaace0f8da6f8950e9bca1d9).


Generating Benchmarks
---------------------
ALIVe will automatically generate benchmarks in SMT-LIB 2 format when the
'bench' directory exists and when python is run in non-optimized mode (the
default).
These benchmarks are over the bit-vector theory and may or may not have
quantifiers.


Regarding Z3's license
----------------------
Z3 is licensed under Microsoft Research License Agreement (MSR-LA), which
forbids commercial usage.
It is, however, our and Microsoft's understanding that using Z3 with ALIVe for
the development of LLVM does not constitute commercial usage for the following
reasons:
 1) LLVM is not a commercial product of any particular company.
 2) ALIVe is free.

Questions regarding Z3's license should be directed to Behrooz Chitsaz
(behroozc@microsoft.com), the Director of IP at Microsoft Research, who kindly
offered to answer any question regarding the usage of Z3 within ALIVe.
This statement does not constitute legal advice and it is not legally binding.
Interested parties should seek professional consultation with an attorney.
