# Permute-and-Flip in SampCert

This directory contains a Lean formalization of the permute-and-flip mechanism
from:

- [McKenna and Sheldon, "Permute-and-Flip: A New Mechanism for Differentially Private Selection"](https://arxiv.org/abs/2010.12603)

It builds on SampCert and refines the mathematical mechanism down to an exact
`SLang` implementation using SampCert's Bernoulli-negative-exponential sampler.

## What Is Proved Here

At a high level, the development proves:

1. A closed-form description of the mechanism's PMF.
2. The monotonicity and regularity properties needed for privacy.
3. A PMF-level privacy theorem.
4. A refinement theorem showing that the exact `SLang` implementation has the
   same privacy guarantee.

The final exported theorems are:

- `permuteAndFlipPMF_range_privacy`
- `permuteAndFlipSLang_range_privacy`

Both are stated using the **range distance** between score vectors:

- `rangeDistance q q' = max_i (q' i - q i) - min_i (q' i - q i)`

This is slightly more general and often tighter than working with a symmetric
`[-1, 1]` perturbation directly.

## Reading Order

If you want the shortest path to the main result, read the files in this order:

1. `Basic.lean`
2. `Privacy.lean`
3. `Monotonicity.lean`
4. `Range.lean`
5. `Mechanism.lean`
6. `Paper.lean`

If you want the executable mechanism first, start with:

1. `Mechanism/Core.lean`
2. `Mechanism/SelectorCore.lean`
3. `Mechanism/Selector.lean`

If you want the paper-style proof first, start with:

1. `Paper/Polynomials.lean`
2. `Paper/Counting.lean`
3. `Paper/ClosedForm.lean`

## File Guide

### Top-level files

- `Basic.lean`
  - Thin facade module.
  - Contains a short paper-to-code map.

- `Privacy.lean`
  - Final privacy-facing theorems.
  - Start here for the end results.

- `Range.lean`
  - Defines the range metric and the normalization gadgets used by the privacy proof.

- `MonotonicityLocal.lean`
  - Local one-coordinate lemmas:
    - raising the selected candidate
    - lowering a competing candidate
  - Contains the hardest local monotonicity argument, including the unique-max case.

- `Monotonicity.lean`
  - Packages the local lemmas into:
    - shift invariance
    - global monotonicity
    - one-step privacy
    - `k`-step privacy contraction

- `Reduction.lean`
  - Abstract regularity-to-privacy reduction on integer-valued score vectors.
  - Also contains the interval and range-distance generalizations.

### Mechanism subdirectory

- `Mechanism/Core.lean`
  - Core score transforms and selector definitions.
  - Defines:
    - `bumpScore`
    - `lowerScore`
    - `gap`
    - `selectPMFCore`
    - `selectSLangCore`

- `Mechanism/SelectorCore.lean`
  - Fixed-order selector weights and canonical-order lemmas.
  - Bridges the recursive selector to a clean closed form for a fixed list order.

- `Mechanism/Selector.lean`
  - Defines the full permute-and-flip mechanism by averaging over uniform random permutations.

### Paper subdirectory

- `Paper/Polynomials.lean`
  - Defines the paper's real-valued quantities:
    - `paperProb`
    - `paperAlt`
    - scaled and primitive variants

- `Paper/Counting.lean`
  - Proves the permutation-counting facts that produce the coefficient
    `1 / (|t| + 1)` in the closed form.

- `Paper/ClosedForm.lean`
  - Connects the actual PMF of the mechanism to the paper's alternating subset sum.

## Proof Strategy

There are two proof viewpoints in the development.

### 1. Executable mechanism viewpoint

The mechanism is defined operationally:

1. sample a uniform random permutation of the candidates,
2. scan candidates in that order,
3. for each candidate `i`, accept with probability `exp(-gap(q,i) * ε₁ / ε₂)`,
4. return the first accepted candidate.

This viewpoint is closest to the implementation and is developed in the
`Mechanism` files.

### 2. Paper closed-form viewpoint

The paper proves privacy using a closed-form PMF expression. The development
reconstructs that proof by:

1. expressing the PMF as an average over permutations,
2. rewriting the permutation average using `beforeSet`,
3. proving the exact subset-event coefficient by combinatorics,
4. identifying the PMF with the paper's alternating subset polynomial.

This viewpoint is developed in the `Paper` files.

## How the Privacy Proof Works

The final privacy proof in `Privacy.lean` is easiest to understand as three steps.

### Step 1: Normalize score differences

Given two score vectors `q` and `q'`, the development looks at the coordinatewise
differences `q' i - q i`. These differences may be negative, so we shift them by
a common constant to obtain natural-valued normalized differences lying in an
interval `[A, B]`.

The width of this interval is exactly `rangeDistance q q'`.

### Step 2: Compare normalized score vectors

After normalization, the proof compares:

- a vector where every coordinate is at the upper endpoint `B`, except `r`,
  which is at the lower endpoint `A`,
- the target normalized vector.

This comparison factors into:

1. a `k`-step privacy contraction for repeatedly raising candidate `r`,
2. a global monotonicity argument saying that raising `r` and lowering others
   can only help output `r`.

### Step 3: Shift back

The mechanism is shift-invariant, so once the normalized comparison is proved,
the result transfers back to the original score vectors `q` and `q'`.

## Paper-to-Code Map

The most useful correspondences are:

- Proposition 2 / regularity reduction
  - `Reduction.reduced_privacy_of_regular`

- Paper closed-form PMF
  - `Paper.ClosedForm.permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt`

- Concrete monotonicity / regularity condition
  - `Monotonicity.permuteAndFlipPMF_monotone`

- One-step privacy contraction
  - `Monotonicity.one_step_privacy`

- Final PMF privacy theorem
  - `Privacy.permuteAndFlipPMF_range_privacy`

- Exact implementation refinement
  - `Privacy.permuteAndFlipSLang_range_privacy`

## Why the Range Metric Appears

The original paper is phrased in terms of score perturbations / sensitivity of
score functions. This development instead states the final theorem directly in
terms of the score vectors themselves using `rangeDistance`.

This has two benefits:

1. it avoids introducing an extra layer of score-function abstraction in the final API,
2. it can give tighter privacy accounting when score changes are monotone and
   differ by a common shift.

## What to Ignore on a First Read

On a first pass, you can safely ignore:

- most helper lemmas in `Mechanism/Core.lean`,
- the scaled primitive helper definitions in `Paper/Polynomials.lean`,
- the lower-level counting bijections in `Paper/Counting.lean`.

The highest-signal route is:

1. read `Privacy.lean`,
2. skim `Monotonicity.lean`,
3. look up specific supporting lemmas only when needed,
4. use `Paper/ClosedForm.lean` if you want to compare directly with the paper.
