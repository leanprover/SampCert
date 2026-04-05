/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.Sparse.Code
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Properties
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Privacy

noncomputable section

open Classical

namespace SLang

variable (T : ℤ) (ε₁ ε₂ : ℕ+) {sv_T : Type}

variable [dps : DPSystem sv_T]
variable [dpn : DPNoise dps]

variable (qs : sv_query sv_T)
-- variable (Hqs : ∀ N : ℕ, has_lucky (shift_qs N qs) T)
variable (Hqs : has_lucky qs T)
variable (HDP : ∀ N H, ∀ ε : NNReal, (ε = ε₁ / ε₂) -> dps.prop (sv1_aboveThresh_PMF (shift_qs N qs) T H ε₁ ε₂) ε)

lemma shift_qs_add {T : Type} (qs' : sv_query T) (A B : ℕ) : (shift_qs A (shift_qs B qs')) = (shift_qs (A + B) qs') := by
  apply funext; simp [shift_qs, add_assoc]

local instance : MeasurableSpace (List ℕ) where
  MeasurableSet' _ := True
  measurableSet_empty := by simp only
  measurableSet_compl := by simp only [imp_self, implies_true]
  measurableSet_iUnion := by simp only [implies_true, imp_self]

local instance : DiscreteMeasurableSpace (List ℕ) where
  forall_measurableSet := by simp only [MeasurableSpace.measurableSet_top, implies_true]

include HDP in
lemma privSparseAux_DP (ε : NNReal) (c : ℕ) (Hε : ε = ε₁ / ε₂) :
    ∀ N : ℕ, ∀ H, dps.prop (privSparseAux T ε₁ ε₂ (shift_qs N qs) H c) (c * ε) := by
  induction c
  · intro _ _
    unfold privSparseAux
    simp
    apply dps.const_prop
    simp_all
  · rename_i c' IH
    intro N HL
    simp [privSparseAux]
    apply dps.postprocess_prop
    apply @DPSystem.adaptive_compose_prop _ _ _ _ _ _ _ _ ε (c' * ε) ((c' + 1) * ε)
    · apply HDP
      trivial
    · intro u
      let IH' := IH (u + N)
      rw [<- shift_qs_add] at IH'
      apply IH'
    · ring_nf

include HDP in
lemma privSparse_DP (ε : NNReal) (c : ℕ) (Hε : ε = ε₁ / ε₂) :
    dps.prop (privSparse T ε₁ ε₂ qs Hqs c) (c * ε) := by
  unfold privSparse
  apply privSparseAux_DP
  · apply HDP
  · trivial
