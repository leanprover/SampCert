/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang
import SampCert.Samplers.Laplace.Code

namespace SLang

def DiscreteLaplaceGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
  let s ← DiscreteLaplaceSample num den
  return s + μ

end SLang
