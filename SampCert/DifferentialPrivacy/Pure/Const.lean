/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Generic
import SampCert.DifferentialPrivacy.Pure.DP

/-!
# zCDP Constant function

This file proves a DP bound on the constant query
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U : Type }

/--
Constant query satisfies zCDP Renyi divergence bound.
-/
theorem privConst_DP_Bound {u : U} : DP (privConst u : Mechanism T U) 0 := by
  rw [event_eq_singleton]
  rw [DP_singleton]
  intros
  simp [privConst]

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem PureDP_privConst : ∀ (u : U),  PureDP (privConst u : Mechanism T U) (0 : NNReal) := by
  simp [PureDP] at *
  apply privConst_DP_Bound

end SLang
