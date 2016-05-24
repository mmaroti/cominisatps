COMiniSatPS simplified
======================

This is a modification of the COMiniSatPS solver that participated in the SAT2015
competition. I have kept only the `core` solver, the `simp` solver is removed.
I am trying to simplify it as much as possible, removing unused parts, and converting
it to the c++11 standard. Ultimately I am trying to understand its inner workings.

## Compilation

Just run `make` in the root directory, this will compile with max optimizations but
assertions enabled. Run `make release` to compile the release version (minimal size)
which disables assertions.
