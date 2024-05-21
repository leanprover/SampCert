/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang

noncomputable section

namespace SLang

def UniformSample (n : PNat) : SLang Nat := do
  let r ← probUntil (uniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
  return r

end SLang
