/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# zCDP Constant function

This file proves a zCDP bound on the constant query
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U : Type }

/--
Constant query satisfies zCDP Renyi divergence bound.
-/
theorem privConst_zCDPBound {u : U} : zCDPBound (privConst u : Mechanism T U) 0 := by sorry

/--
Constant query satisfies absolute continuity
-/
def privConst_AC {u : U} : ACNeighbour (privConst u : Mechanism T U) := by sorry

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privConst_zCDP : ∀ (u : U), zCDP (privConst u : Mechanism T U) 0 := by
  simp [zCDP] at *
  intro u
  apply And.intro
  · apply privConst_AC
  · apply privConst_zCDPBound
end SLang
