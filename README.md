# Verifying Differential Privacy in Lean

The [SampCert](https://github.com/leanprover/SampCert) project (de Medeiros et al. 2024) was created to implement and formalize differential privacy notions in Lean. It provided support for various notions of differential privacy, a framework for implementing differentially private mechanisms via verified sampling algorithms, and implemented several differentially private algorithms, including the Gaussian and Laplace mechanisms.

We build upon SampCert, creating support for the local model using [Lean](https://lean-lang.org/) and the extensive [Mathlib](https://github.com/leanprover-community/mathlib4) library. We also implement the [randomized response](https://www.tandfonline.com/doi/abs/10.1080/01621459.1965.10480775) and [one-time basic RAPPOR](https://static.googleusercontent.com/media/research.google.com/en//pubs/archive/42852.pdf) mechanisms, as well as implementing a more robust post-processing property for randomized mappings. We additionally move towards an implementation of the shuffle model.

Our implementations are in `SampCert/DifferentialPrivacy/Pure`. Our additions are in the Local folder, Shuffle Model folder, and a few separate files in the Pure folder.

### Local

#### BinomialSample

We implement and show normalization for a sampler for the Binomial distribution.

#### LocalDP

The files in this folder provide a variety of definitions to support the local model of differential privacy. We create a definition of differential privacy that is parametrized by a neighbour relation, thus generalizing the SampCert definition. For the local model, we use the `DP_withUpdateNeighbour` definition of neighboring datasets, which considers two lists to be neighbouring if they differ in the update of a single entry.

We also show that if an $\epsilon$-local randomizer is extended to a dataset via monadic map, the resulting algorithm is $\epsilon$-differentially private. This is proven in `LocalDP_toDataset.`

#### MultiBernoulli

The files here implement and show normalization for the "multi-Bernoulli" distribution, which we define to be the distribution associated with flipping each entry of a list independently and with the same probability.

#### RAPPOR

In this folder, we provide an implementation of basic one-time RAPPOR and give a proof of differential privacy. The file `Definitions.lean` provides our implementation of RAPPOR. The file `Properties/DPProof.lean` provides a proof that our implementation of RAPPOR is differentially private.

#### RandomizedResponse

In this folder, we provide an implementation of randomized response and give a proof of differential privacy. The file `Definitions.lean` provides our implementation of randomized response. The file `Properties/DPProof.lean` provides a proof that our implementation of randomized response is differentially private.

#### ProbabilityProduct.lean

We show that the probability of generating a list of outputs is equal to the product of the probabilities of generating each output independently. This is used to prove our `LocalDP_toDataset` lemma.
#### PushForward.lean

We prove that the push-forward of a probability measure is a probability measure. A similar statement already exists in SampCert, but our rephrasing was slightly more convenient for our purposes.
#### Reduction.lean

We prove a helper lemma that is used in proving a local algorithm is DP. It allows us to reduce the problem to just considering the local randomizer.

### Shuffle model

This folder contains the implementation and properties of the shuffle model.

#### Definitions.lean

This contains the definition of the shuffle model. The definition `Shuffler` is the randomized permutation. We implement the shuffle algorithm with randomized response in `RRShuffle`, and provide a more general definition in `ShuffleAlgorithm`.

#### Properties.lean

This instantiates the shuffle algorithm as a PMF, and show that the algorithm for a random permutation that we define is uniform. In the theorem `ShuffleAlgorithm_is_DP`, we show that shuffling the output of a differentially-private algorithm does not worsen the differential privacy bound. 

#### ENNRealLemmaSuite.lean

A significant challenge in our work was proving arithemetic statements over extended non-negative reals. Mathlib currently provides less support for arithmetic in the ENNReal type, so oftentimes we have to prove statements ourselves. These statements are in this file.

#### LawfulMonadSLang.lean

We instantiate SLang as a LawfulMonad. 

#### Normalization.lean

We prove a lemma showing that the mass of a distribution is preserved under monadic map. This is used for both of the local algorithms that we implemented.

### RandomizedPostProcess.lean

This file provides the Lean proof about the post-processing property of differential privacy: If there is an $\epsilon$-DP mechanism $M: X \rightarrow W$ and a (possibly randomized) mapping $F: W \rightarrow Z$, then $F \circ M$ is $\epsilon$-DP. The case where $F$ is deterministic is implemented in SampCert. We implement the case where $F$ is random. The result is in the lemma 
``lemma randPostProcess_DP_bound_with_UpdateNeighbour``.

We would like to thank SampCert for motivating and being the basis for our project. We would also like to thank Google for sponsoring and mentoring this project, and the Institute of Pure and Applied Mathematics (IPAM) for supporting and hosting our work.
