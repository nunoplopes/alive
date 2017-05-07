Translation Validation with Alive
=================================

This directory contains a set of simple scripts to do translation
validation of LLVM with Alive.


Usage
-----
Given a file.ll and an optimization that you want to test (say,
InstCombine), run the following:
 * opt -S -instcombine file.ll -o file.instcombine.ll
 * python tv.py instcombine file > instcombine/file.txt

If you run many tests and wish to filter the results, run:
 * php filter.php instcombine

This will filter out correct optimizations and bad transformations that
you may not be interested in (e.g., involving select of undef).  Tweak
the script per your use case.


Generating inputs
-----------------
To exhaustively generate a large set of inputs, you can use opt-fuzz
from https://github.com/regehr/opt-fuzz


Limitations
-----------
Alive can only verify the correctness of a subset of transformations
that LLVM does.  Alive's language can only handle forward jumps, and
basic blocks have to be given topologically sorted.  Support for
memory and pointer manipulation is limited.
In practice, this means that translation validation of loop-manipulating
optimizations does not work.
