/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang

/-!
# ``UniformSample`` Implementation

This file contains the implementation for a uniform sampler over a finite set.

## Implementation Notes
``UniformSample`` violates our naming scheme, but this is currently necessary for extraction.
-/

namespace SLang

/-- ``Slang`` term for a uniform sample over [0, n). Implemented using rejection sampling on
  top of the power of two uniform sampler ``probUniformP2``. -/
def UniformSample (n : PNat) : SLang Nat := do
  let r ← probUntil (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
  return r

end SLang
