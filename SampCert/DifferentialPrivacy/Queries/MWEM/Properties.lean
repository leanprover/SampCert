/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Queries.MWEM.Code
import SampCert.DifferentialPrivacy.Queries.ReportNoisyMax.Basic
import SampCert.DifferentialPrivacy.Pure.System

/-!
# Privacy of MWEM

Each round of MWEM is `2(ε₁/ε₂)`-DP by adaptive composition of Report-Noisy-Max
and the Laplace mechanism, both `(ε₁/ε₂)`-DP under the sensitivity hypotheses
of `SyntheticUpdater`. The synthetic state update is post-processing of the
selection-and-measurement transcript, so it adds no privacy cost. By induction
over `T` rounds, MWEM is `2T(ε₁/ε₂)`-DP.
-/

noncomputable section

open Classical Nat Int Real ENNReal

namespace SLang

variable {X : Type} {n : ℕ} {Δ : ℕ+} {State : Type} {init : State}

instance : MeasurableSpace (Fin (n+1) × ℤ) := ⊤
instance : DiscreteMeasurableSpace (Fin (n+1) × ℤ) where
  forall_measurableSet _ := .congr trivial rfl

instance : MeasurableSpace (List (Fin (n+1) × ℤ)) := ⊤
instance : DiscreteMeasurableSpace (List (Fin (n+1) × ℤ)) where
  forall_measurableSet _ := .congr trivial rfl

theorem mwemRound_DP (U : SyntheticUpdater X n Δ State init) (ε₁ ε₂ : ℕ+) (ε : NNReal)
    (HN : laplace_pureDP_noise_priv ε₁ ε₂ ε) (A : State) :
    PureDPSystem.prop (mwemRound U ε₁ ε₂ A) (ε + ε) :=
  PureDPSystem.adaptive_compose_prop
    (privReportNoisyMax_DP n (U.scoreFn A) Δ ε₁ ε₂ ε HN (U.scoreFn_sens A))
    (fun i => privNoisedQueryPure_DP (U.queries i) Δ ε₁ ε₂ ε HN (U.queries_sens i))
    rfl

theorem mwem_DP (U : SyntheticUpdater X n Δ State init) (ε₁ ε₂ : ℕ+) (ε : NNReal)
    (HN : laplace_pureDP_noise_priv ε₁ ε₂ ε) (T : ℕ) (A : State) :
    PureDPSystem.prop (mwem U ε₁ ε₂ T A) (T * (ε + ε)) := by
  induction T generalizing A with
  | zero => exact PureDPSystem.const_prop (by push_cast; ring)
  | succ T IH =>
    refine PureDPSystem.postprocess_prop <|
      PureDPSystem.adaptive_compose_prop (mwemRound_DP U ε₁ ε₂ ε HN A)
        (fun im => IH (U.update A im.1 im.2)) ?_
    push_cast; ring

theorem mwemSPMF_DP (U : SyntheticUpdater X n Δ State init) (ε₁ ε₂ : ℕ+) (ε : NNReal)
    (HN : laplace_pureDP_noise_priv ε₁ ε₂ ε) (T : ℕ) (A : State) :
    PureDPSystem.prop (mwemSPMF U ε₁ ε₂ T A) (T * (ε + ε)) := by
  have heq : (fun l => mwemSPMF U ε₁ ε₂ T A l) = (fun l => (mwem U ε₁ ε₂ T A l : SPMF _)) := by
    funext l
    apply Subtype.ext
    exact mwemSLang_eq U ε₁ ε₂ T A l
  rw [show mwemSPMF U ε₁ ε₂ T A = _ from heq]
  exact mwem_DP U ε₁ ε₂ ε HN T A

end SLang

end
