/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Samplers.LaplaceGen.Code
import SampCert.Samplers.Laplace.Properties

noncomputable section

open Classical PMF Nat Real

namespace SLang

theorem DiscreteLaplaceGenSample_apply (num : PNat) (den : PNat) (μ x : ℤ) :
  (DiscreteLaplaceGenSample num den μ) x =
  ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs (x - μ) / ((num : NNReal) / (den : NNReal)))))) := by
  sorry

end SLang
