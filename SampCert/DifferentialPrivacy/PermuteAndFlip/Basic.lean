import SampCert.DifferentialPrivacy.PermuteAndFlip.Privacy

/-!
Facade module for the permute-and-flip development.

Paper-to-code map:
- Proposition 2 / regularity reduction:
  [Reduction.reduced_privacy_of_regular](SampCert/DifferentialPrivacy/PermuteAndFlip/Reduction.lean)
- Closed-form PMF bridge used in the proof of Theorem 1:
  [Paper.ClosedForm.permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt](SampCert/DifferentialPrivacy/PermuteAndFlip/Paper/ClosedForm.lean)
- Regularity / monotonicity for permute-and-flip:
  [Monotonicity.permuteAndFlipPMF_monotone](SampCert/DifferentialPrivacy/PermuteAndFlip/Monotonicity.lean)
- Final PMF privacy theorem:
  [Privacy.permuteAndFlipPMF_range_privacy](SampCert/DifferentialPrivacy/PermuteAndFlip/Privacy.lean)
- Exact `SLang` refinement:
  [Privacy.permuteAndFlipSLang_range_privacy](SampCert/DifferentialPrivacy/PermuteAndFlip/Privacy.lean)

Main entry theorems:
- `permuteAndFlipPMF_range_privacy`
- `permuteAndFlipSLang_range_privacy`

For implementation details, start with:
- `Mechanism` for the executable mechanism and its permutation-averaged PMF
- `Paper` for the paper-style PMF derivation
- `Range` for the range-distance metric layer
- `MonotonicityLocal` for the local bump/lower lemmas
- `Monotonicity` for the global monotonicity and privacy-step lemmas
- `Privacy` for the final exported privacy theorems
-/
