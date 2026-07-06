# Permute-and-Flip in SampCert

A Lean formalization of the permute-and-flip selection mechanism of McKenna and
Sheldon, ["Permute-and-Flip: A New Mechanism for Differentially Private
Selection"](https://arxiv.org/abs/2010.12603). The development starts from the
mathematical mechanism and refines it down to an exact `SLang` implementation
built on SampCert's Bernoulli-negative-exponential sampler.

## Results

The two exported theorems live in `Privacy.lean`:

- `permuteAndFlipPMF_range_privacy`, privacy of the mechanism's PMF;
- `permuteAndFlipSLang_range_privacy`, the same guarantee for the executable
  `SLang` implementation.

Both are stated in terms of the range distance between score vectors,

    rangeDistance q q' = max_i (q' i - q i) - min_i (q' i - q i),

rather than a symmetric `[-1, 1]` perturbation. Stating privacy directly on the
score vectors keeps the final API free of an extra score-function abstraction,
and it gives tighter accounting when the score changes are monotone and differ
by a common shift.

Reaching those theorems requires a closed form for the PMF, the monotonicity and
regularity properties the privacy argument depends on, and the refinement
theorem tying the `SLang` implementation back to the PMF.

## Files

`Basic.lean` is a facade that pulls in the development and carries the
paper-to-code map. `Privacy.lean` holds the final theorems and is the place to
start.

The privacy argument is spread across:

- `Range.lean`, the range metric and the normalization gadgets used by the proof;
- `MonotonicityLocal.lean`, the one-coordinate lemmas for raising the selected
  candidate and lowering a competitor, including the delicate unique-max case;
- `Monotonicity.lean`, which assembles those into shift invariance, global
  monotonicity, and the one- and `k`-step privacy contractions;
- `Reduction.lean`, a standalone abstract reduction from regularity to privacy
  on integer-valued score vectors, with interval and range-distance
  generalizations (namespace `SLang.PermuteAndFlip.Reduction`).

The mechanism itself lives in `Mechanism/`:

- `Core.lean`, the score transforms, gaps, recursive selector, and exact sampler;
- `SelectorCore.lean`, selector weights and canonical-order lemmas for a fixed
  candidate order;
- `Selector.lean`, the mechanism as an average over uniform random permutations.

The paper-style closed form lives in `Paper/`:

- `Polynomials.lean`, the paper's real-valued quantities (`paperProb`,
  `paperAlt`, and their variants);
- `Counting.lean`, the permutation-counting facts behind the `1 / (|t| + 1)`
  coefficient;
- `ClosedForm.lean`, which identifies the mechanism's PMF with the paper's
  alternating subset sum.

## The mechanism

Operationally, permute-and-flip

1. samples a uniform random permutation of the candidates,
2. scans them in that order,
3. accepts candidate `i` with probability `exp(-gap(q, i) * ε₁ / ε₂)`,
4. and returns the first accepted candidate.

The `Mechanism` files develop this operational form. The `Paper` files develop
the alternative closed-form PMF: the permutation average is rewritten using
`beforeSet`, the subset-event coefficient is computed by combinatorics, and the
resulting expression is matched to the paper's alternating subset polynomial.

## The privacy proof

`Privacy.lean` works in three steps. Given score vectors `q` and `q'`, the
coordinatewise differences `q' i - q i` may be negative, so they are shifted by a
common constant into a natural-valued interval `[A, B]` whose width is exactly
`rangeDistance q q'`. The proof then compares the normalized target vector
against the vector sitting at the upper endpoint `B` in every coordinate except
the chosen candidate `r`, which sits at `A`. That comparison factors into a
`k`-step contraction that repeatedly raises `r`, together with a monotonicity
argument showing that raising `r` while lowering the others can only favor `r`.
Since the mechanism is shift-invariant, the normalized comparison transfers back
to the original `q` and `q'`.

## Paper-to-code map

- Proposition 2, the regularity reduction: `Reduction.reduced_privacy_of_regular`
- Closed-form PMF: `Paper.ClosedForm.permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt`
- Concrete monotonicity / regularity: `Monotonicity.permuteAndFlipPMF_monotone`
- One-step privacy contraction: `Monotonicity.one_step_privacy`
- Final PMF privacy theorem: `Privacy.permuteAndFlipPMF_range_privacy`
- Exact implementation refinement: `Privacy.permuteAndFlipSLang_range_privacy`
