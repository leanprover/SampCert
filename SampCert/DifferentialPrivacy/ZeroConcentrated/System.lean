/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.Composition
import SampCert.DifferentialPrivacy.ZeroConcentrated.AdaptiveComposition
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing

/-!
# zCDP System

This file contains an instance of an abstract DP system associated to the discrete gaussian mechanisms.
-/

namespace SLang

variable { T : Type }

/--
Instance of a DP system for zCDP, using the discrete Gaussian as a noising mechanism.
-/
noncomputable instance gaussian_zCDPSystem : DPSystem T where
  prop := zCDP
  noise := privNoisedQuery
  noise_prop := privNoisedQuery_zCDP
  compose_prop := privCompose_zCDP
  adaptive_unif_prop := fun {Z U} nq2 =>
    ((∃ (z : ℝ), ∀ (u : U), ∀ l, ∑'(v : Z), nq2 u l v ≤ ENNReal.ofReal z) ∧
     (URDBound nq2 (fun α l₁ l₂ => ⨆ u, RenyiDivergence (nq2 u l₁) (nq2 u l₂) α)))
  adaptive_compose_prop := by
    intros
    apply privComposeAdaptive_zCDP <;> aesop
  postprocess_prop := privPostProcess_zCDP

end SLang
