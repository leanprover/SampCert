# SampCert

A verified implementation using [Lean](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) of randomized algorithms including [the discrete Gaussian sampler for differential privacy](https://arxiv.org/abs/2004.00010), key results in [zero concentrated differential privacy](https://arxiv.org/abs/1605.02065), and [some verified (unbounded) private queries](https://arxiv.org/pdf/1909.01917).

SampCert is deployed and used in the [AWS Clean Rooms Differential Privacy service](https://docs.aws.amazon.com/clean-rooms/latest/userguide/differential-privacy.html#dp-overview). SampCert proves deep properties about some of its randomized algorithm and makes heavy use of Mathlib. For example, we use theorems such as [the Poisson summation formula](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/PoissonSummation.html#Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay).

The principal developer of SampCert is [Jean-Baptiste Tristan](https://jtristan.github.io/). It is also developed by [Markus de Medeiros](https://www.markusde.ca/). 

Other people have contributed important ideas or tools for deployment including (in no particular order): Leo de Moura, Anjali Joshi, Joseph Tassarotti, Stefan Zetzsche, Aws Albharghouti, Muhammad Naveed, Tristan Ravitch, Fabian Zaiser, Tomas Skrivan.

To cite SampCert you can currently use the following reference:
```
@software{Tristan_SampCert_Verified_2024,
author = {Tristan, Jean-Baptiste},
doi = {10.5281/zenodo.11204806},
month = may,
title = {{SampCert : Verified Differential Privacy}},
url = {https://github.com/leanprover/SampCert},
version = {1.0.0},
year = {2024}
}
```
