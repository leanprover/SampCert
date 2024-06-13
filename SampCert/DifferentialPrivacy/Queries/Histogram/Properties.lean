/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.Histogram.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privHistogram`` Properties

This file proves abstract differential privacy for the noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

variable (numBins : ℕ+)
variable (B : Bins T numBins)

-- def exactBinCount (b : Fin num_bins) (l : List T) : ℤ :=
--   List.length (List.filter (fun v => B.bin v = b) l)

/-
exactBinCount is 1-sensitive
-/
theorem exactBinCount_sensitivity (b : Fin numBins) : sensitivity (exactBinCount numBins B b) 1 := by
  rw [sensitivity]
  intros l₁ l₂ HN
  cases HN
  · rename_i l₁' l₂' v' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v' l₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v₁' l₂' v₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    -- There has to be a better way
    cases (Classical.em (B.bin v₁' = b)) <;> cases (Classical.em (B.bin v₂' = b))
    all_goals (rename_i Hrw1 Hrw2)
    all_goals (simp [Hrw1, Hrw2])

/--
DP bound for a noised bin count
-/
lemma privNoisedBinCount_DP (ε₁ ε₂ : ℕ+) (b : Fin numBins) :
  dps.prop (privNoisedBinCount numBins B ε₁ ε₂ b) (ε₁ / ((ε₂ * numBins : PNat))) := by
  unfold privNoisedBinCount
  apply dps.noise_prop
  apply exactBinCount_sensitivity

/--
DP bound for intermediate steps in the histogram calculation.
-/
lemma privNoisedHistogramAux_DP (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) :
  dps.prop (privNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (n.succ * (ε₁ / (ε₂ * numBins : PNat))) := by
  induction n
  · unfold privNoisedHistogramAux
    simp only [Nat.cast_zero, succ_eq_add_one, zero_add, Nat.cast_one, Nat.cast_mul, one_mul]
    apply dps.postprocess_prop
    · unfold Function.Surjective
      intro h
      exists (h.count.get (Fin.mk 0 Hn), h)
      simp
      rw [setCount]
      cases h
      simp
      apply Vector.ext
      intro m
      rw [Vector.get_set_eq_if]
      split
      · rename_i Hm
        rw [<- Hm]
        congr
        simp
        exact Eq.symm (Nat.mod_eq_of_lt Hn)
      · rfl
    -- Should be able to prove abstractly that the constant function is DP
    -- Maybe follows from value dependent composition?
    sorry
  · rename_i n IH
    unfold privNoisedHistogramAux
    simp only []
    have Hn_pos : 0 < n + 1 := by aesop
    refine (privPostProcess_ext ?succ.surj
           (privCompose (privNoisedBinCount numBins B ε₁ ε₂ ↑(n + 1))
           (privNoisedHistogramAux numBins B ε₁ ε₂ n (privNoisedHistogramAux.proof_2 numBins n Hn)))
           ((⟨ n + 1, Hn_pos ⟩ + 1) * ε₁) (ε₂ * numBins)
           (↑(n + 1).succ * (↑↑ε₁ / ↑↑(ε₂ * numBins))) ?succ.a1 ?succ.εEq)
    case succ.εEq =>
      simp
      sorry
      -- exact Eq.symm (mul_div_assoc (↑n + 1 + 1) (↑↑ε₁) (↑↑ε₂ * ↑↑numBins))
    case succ.surj =>
      unfold Function.Surjective
      intro h
      exists (h.count.get (Fin.mk (n + 1) Hn), h)
      simp
      rw [setCount]
      cases h
      rename_i count
      simp
      apply Vector.ext
      intro m
      rw [Vector.get_set_eq_if]
      split
      · rename_i Hm
        rw [<- Hm]
        congr
        simp
        exact Eq.symm (Nat.mod_eq_of_lt Hn)
      · rfl

    refine (privCompose_ext (privNoisedBinCount numBins B ε₁ ε₂ ↑(n + 1))
            (privNoisedHistogramAux numBins B ε₁ ε₂ n (privNoisedHistogramAux.proof_2 numBins n Hn))
            ε₁ (ε₂ * numBins) (⟨ n + 1, Hn_pos ⟩ * ε₁) (ε₂ * numBins)
            (↑↑((⟨ n + 1, Hn_pos ⟩ + 1 : PNat) * ε₁) / ↑↑(ε₂ * numBins)) ?succ.a1.DPCount ?succ.a1.DPrec ?succ.a1.εEq)
    case succ.a1.εEq =>
      rw [div_add_div_same]
      simp
      congr
      -- have Hrw : ε₁ = 1 * (ε₁ : ℝ) := by exact?
      conv =>
        rhs
        arg 1
        rw [one_mul]


      sorry
    case succ.a1.DPCount => sorry
    case succ.a1.DPrec => sorry


/--
DP bound for a noised histogram
-/
lemma privNoisedHistogram_DP (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedHistogram numBins B ε₁ ε₂) (ε₁ / ε₂) := by
  unfold privNoisedHistogram
  have H : (↑↑ ε₁ / ↑↑ ε₂ : ℝ) = ↑(predBins numBins).succ * (↑↑ε₁ / ↑↑(ε₂ * numBins)) := by
    rw [cast_succ]
    rw [predBins]
    rw [PNat.natPred]
    simp
    rw [div_mul_eq_div_div]
    -- Doable
    sorry
  rw [H]
  apply (privNoisedHistogramAux_DP numBins B ε₁ ε₂ (predBins numBins) (predBins_lt_numBins numBins))


/--
DP bound for the thresholding maximum
-/
lemma privMaxBinAboveThreshold_DP (ε₁ ε₂ : ℕ+) (τ : ℤ) :
  dps.prop (privMaxBinAboveThreshold numBins B ε₁ ε₂ τ) (ε₁ / ε₂) := by
  rw [privMaxBinAboveThreshold]
  apply dps.postprocess_prop
  · sorry
  · apply privNoisedHistogram_DP

end SLang
