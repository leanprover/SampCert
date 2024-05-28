# SampCert

A verified implementation using [Lean](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) of [the discrete Gaussian sampler for differential privacy](https://arxiv.org/abs/2004.00010), the composition and postprocessing of zero concentrated differential privacy, and some simple queries.

The Lean implementation is not computable because algorithms that terminate with probability 1 are defined using a combinator. However, the code can be extracted to [Dafny](https://dafny.org/) and used as part of the [VMC library](https://github.com/dafny-lang/Dafny-VMC).  

Contributors: Jean-Baptiste Tristan, Leo de Moura, Anjali Joshi, Joseph Tassarotti.
