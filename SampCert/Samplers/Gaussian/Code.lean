/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code

/-!
# ``DiscreteGaussianSample`` Implementation

## Implementation Notes

The following identifiers violate our naming scheme, but are currently necessary for extraction:
  - ``DiscreteGaussianSampleLoop``
  - ``DiscreteGaussianSample``
-/

namespace SLang

/--
Sample a candidate for the Discrete Gaussian with variance ``num/den``.
-/
def DiscreteGaussianSampleLoop (num den t : PNat) (mix : ℕ) : SLang (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSampleMixed t 1 mix
  let y : Nat := Int.natAbs Y
  let n : Nat := (Int.natAbs (Int.sub (y * t * den) num))^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

/--
``SLang`` term to sample a value from the Discrete Gaussian with variance ``(num/den)``^2.
-/
def DiscreteGaussianSample (num : PNat) (den : PNat) (mix : ℕ) : SLang ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , by simp only [add_pos_iff, zero_lt_one, or_true] ⟩
  let num := num^2
  let den := den^2
  let r ← probUntil (DiscreteGaussianSampleLoop num den t mix) (λ x : Int × Bool => x.2)
  return r.1

end SLang
