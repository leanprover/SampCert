# Verifying Differential Privacy in Lean

The [SampCert](https://github.com/leanprover/SampCert) project (de Medeiros et al. 2024) was created to implement and formalize differential privacy notions in Lean. It provided support for various notions of differential privacy, a framework for implementing differentially private mechanisms via verified sampling algorithms, and several differentially private algorithms, including the Gaussian and Laplace mechanisms.

We build upon SampCert, creating support for the local model using [Lean](https://lean-lang.org/) and the extensive [Mathlib](https://github.com/leanprover-community/mathlib4) library. We also implement the [randomized response](https://www.tandfonline.com/doi/abs/10.1080/01621459.1965.10480775) and [one-time basic RAPPOR](https://static.googleusercontent.com/media/research.google.com/en//pubs/archive/42852.pdf) mechanisms, as well as implementing a more robust post-processing property for randomized mappings. We additionally move towards an implementation of the shuffle model.

Our implementations are in SampCert/DifferentialPrivacy/Pure. Our additions are in the Local folder, Shuffle Model folder, and RandomizedPostProcessing.lean file. 

### Local

#### BinomialSample

#### LocalDP

The files in this folder provide a variety of lemmas to support general ideas about the local model of DP. A key lemma here is `DP_withUpdateNeighbour`, which defines differential privacy with an user provided definition of neighbour. This provides more functionality than the Add-Remove-Update definition of neighbour in SampCert.

Another key idea is `LocalDP_to_dataset`. A key idea in the local model is that if an algorithm on an individual user is $\epsilon$-DP, then the algorithm on the entire dataset is $\epsilon$-DP. This lemma shows that.

#### MultiBernoulli

The files here provide some helper lemmas related to the Bernoulli distribution. Drawing from the Bernoulli distribution is needed for our implementation of randomized response.

#### RAPPOR

In this folder, we provide an implementation of basic one-time RAPPOR and give a proof of differential privacy. The file Definitions.lean provides our implementation of RAPPOR. The file `Properties/DPProof.lean` provides a proof that our implementation of RAPPOR is differentially private.

#### RandomizedResponse

In this folder, we provide an implementation of randomized response and give a proof of differential privacy. The file Definitions.lean provides our implementation of randomized response. The file `Properties/DPProof.lean` provides a proof that our implementation of randomized response is differentially private.

#### ENNRealLemmaSuites.lean

A significant challenge was proving arithemetic states over ENNReal. Mathlib currently provides less support for arithmetic over ENNReal, so oftentimes we have to prove statements ourselves. These statements are in this file.

#### LawfulMonadSLang.lean

Instantiates SLang as a LawfulMonad.

#### Normalization.lean

Lemmas relating to proving that applying a monadic map to a normalized function remains normalized.

#### ProbabilityProduct.lean

Shows that the probability of generating a sequence of outputs is equal to the product of the probabilities of generating each output independently. Used in randomized response and RAPPOR.

#### PushForward.lean



#### Reduction.lean

Helper function used in proving a local algorithm is DP. Allows us to reduce the problem from considering the entire dataset to the local randomizer.

### Shuffle model

This folder contains the implementation and properties of the shuffle model.

#### Definitions.lean

This contains the definition of the shuffle model. The definition `Shuffler` is the randomized permutation. We implement the shuffle model with randomized response in `RRShuffle`, and provide a more general definition in `ShuffleAlgorithm`.

#### Properties.lean

This contains a variety of proofs that show that the shuffle model indeed outputs a PMF, and that the random permutation is uniform. The theorem `ShuffleAlgorithm_is_DP` also proves that the shuffle model is differentially private using the post-processing property.

### RandomizedPostProcess.lean

This file provides the Lean proof about the post-processing property of differential privacy: If there is an $\epsilon$-DP mechanism $M: X \rightarrow W$ and a (possibly randomized) mapping $F: W \rightarrow Z$, then $F \circ M$ is $\epsilon$-DP. The case where $F$ is deterministic is implemented in SampCert. We implement the case where $F$ is random. The result is in the lemma 
``lemma randPostProcess_DP_bound_with_UpdateNeighbour``.



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
