/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang

/-! # Implementation for a Unifrom Sampler over a finite set -/

noncomputable section

namespace SLang

-- MARKUSDE: Why is it implemented this way?
/-- ``Slang`` term for a uniform sample over [0, n). Implemented using rejection sampling on
    the uniform sampler on a space whose size is a power of two. -/
-- MARKUSDE: FIXME-- violates the naming scheme
def UniformSample (n : PNat) : SLang Nat := do
  let r ← probUntil (probUniformP2 (2 * n)) (λ x : Nat => x < n)
  return r

end SLang
