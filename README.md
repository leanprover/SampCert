# Verifying Differential Privacy in Lean

The [SampCert](https://github.com/leanprover/SampCert) project (de Medeiros et al. 2024) was created to implement and formalize differential privacy notions in Lean. It provided support for various notions of differential privacy, a framework for DP mechanisms, and the Gaussian and Laplace mechanisms.

We build upon SampCert, creating support for the local model using [Lean](https://lean-lang.org/) and the extensive [Mathlib](https://github.com/leanprover-community/mathlib4) library. We also implement the [randomized response](https://www.tandfonline.com/doi/abs/10.1080/01621459.1965.10480775) and [one-time basic RAPPOR](https://static.googleusercontent.com/media/research.google.com/en//pubs/archive/42852.pdf) mechanisms, as well as implement a more robust post-processing property for randomized mappings.



We would like to thank SampCert for motivating and being the basis for our project.
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
