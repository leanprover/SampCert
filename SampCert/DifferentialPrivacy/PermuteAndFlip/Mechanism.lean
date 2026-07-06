/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.Core
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.SelectorCore
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.Selector

/-!
Reader-facing entry point for the executable permute-and-flip mechanism.

Reading order:
- `Mechanism.Core` defines scores, gaps, the recursive selector core, and the exact sampler.
- `Mechanism.SelectorCore` proves selector-weight and canonical-order lemmas.
- `Mechanism.Selector` builds the permutation-averaged PMF and `SLang` mechanism.

Key definitions and theorems:
- `permuteAndFlipPMF`
- `permuteAndFlipSLang`
- `permuteAndFlipSLang_eq_permuteAndFlipPMF`
- `permuteAndFlipPMF_eq_coin_mul_tsum_beforeSet_prod`
-/
