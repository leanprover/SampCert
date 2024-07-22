/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Samplers.Gaussian.Code

/-!
# ``DiscreteGaussianGenSample`` Implementation

## Implementation Note
The identifier ``DiscreteGaussianGenSample`` violates our naming scheme, however we will keep it
this way for parity with ``DiscreteGaussianGen``.
-/

namespace SLang

/--
``SLang`` implementation of a discrete gaussian with mean ``μ`` and variance ``(num/den)^2``.
-/
def DiscreteGaussianGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
  let s ← DiscreteGaussianSample num den 7
  return s + μ

end SLang
