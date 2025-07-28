import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.Samplers.Bernoulli.Properties

-- UNDER CONSTRUCTION --
--DO NOT USE. USE DPProof2.lean--

/-
lemma final_transition (num : Nat) (den : PNat) (h : 2 * num < den) : (den + (2 : ENNReal) * num) / (den - 2 * num) = ((1/2 + num/den) / (1/2 - num/den)) := by
  rw [← mul_div_mul_left 2 (1/2 + num/den) (1/2 - num/den)]
  sorry


lemma final_bound {γ: ℝ} (h0: 0 ≤ γ) (h1: 1/2 > γ) :
ENNReal.ofReal ((1/2 + γ) / (1/2 - γ) )≤ ENNReal.ofReal (Real.exp (Real.log ((1/2 + γ) / (1/2 - γ)))) := by
  rw []
  have h_pos : 0 < (1 / 2 : ℝ) - γ := sub_pos.mpr h1
  have num_pos : 0 < 1 / 2 + γ := by linarith
  exact div_pos num_pos h_pos


lemma pos_helper (num : Nat) (den : PNat):
  0 < ((1:ℝ) / 2 + ↑num / ↑(NNReal.ofPNat den)) := by
  apply add_pos_of_pos_of_nonneg
  norm_num
  apply div_nonneg
  exact Nat.cast_nonneg num
  exact NNReal.coe_nonneg (NNReal.ofPNat den)

lemma num_div_lt_one_half (num : Nat) (den : PNat) (h : 2 * num < den) :
  ↑num / ↑↑↑den < (2⁻¹ : ℝ) := by

lemma nnreal_coe_ineq (n : Nat) (d : PNat) (h : n < d.val) : n < NNReal.ofPNat d := by aesop

lemma t (num : ℕ) (den : PNat) (h : 2 * num < den) : 2 * ↑num < NNReal.ofPNat den := by
  simp
  norm_cast

lemma tr (num : ℕ) (den : ℕ+) (h : 2 * num < den) :
  (1 / 2 : NNReal) * (2 * ↑num) < (1 / 2 : NNReal) * NNReal.ofPNat den := by
  rw [← mul_assoc]
  rw [← inv_eq_one_div]
  rw [inv_mul_cancel]
  rw [one_mul]
  rw [← mul_lt_mul_iff_of_pos_left two_pos]
  rw [← mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]
  {exact t num den h}
  {norm_num}
  {norm_num}

lemma temp (num : Nat) (den : PNat) (h : 2 * num < den) :  (num : ℝ) / den < (1 : ℝ) / 2:= by
  rw [div_lt_iff]
  {
   have h2: 1/2 * (2 * ↑num) < 1/2 * NNReal.ofPNat den := tr num den h
   have h3: 1/2 * (2 * (num : NNReal)) = (1/2 * 2) * ↑num := by aesop
   have h4: (1/2 * 2) * (num : NNReal) = num := by aesop
   rw [h3] at h2
   rw [h4] at h2
   exact h2
  }
  {simp [den.pos]
   exact den.2}

lemma bruh1 (num : Nat) (den : PNat) (h: 2 * num < den) :
  0 < ((1:ℝ) / 2 - ↑num / ↑(NNReal.ofPNat den)) := by
  have h1 : 1/2 > (num : ℝ) / den := temp num den h
  have h_pos : 0 < (1 / 2 : ℝ) - (num / den) := sub_pos.mpr h1
  exact h_pos


lemma final_step (num : Nat) (den : PNat) (h: 2 * num < den):
  (1/2 + num/den) / (1/2 - num/den) ≤ Real.exp (Real.log ((1/2 + num/den) / (1/2 - num/den))) := by
  rw [Real.exp_log]
  rw [@div_pos_iff]
  apply Or.inl
  apply And.intro
  {apply pos_helper}
  {apply bruh1 num den h}

  /- have h1 : 0 < ((1: ℝ) / 2 + ↑num / ↑(NNReal.ofPNat den)) := bruh query num den h l
  have h2 : 0 < ((1:ℝ) / 2 - ↑num / ↑(NNReal.ofPNat den)) := bruh1 query num den h l
  apply div_pos h1 h2 -/

lemma ennreal_pres_ineq (a b : Real): a ≤ b -> ENNReal.ofReal a ≤ ENNReal.ofReal b := by sorry

lemma q (num : Nat) (den : PNat) (h : 2 * num < den) :
  (1/(2 : ENNReal) + num/den) / (1/2 - num/den) = ENNReal.ofReal (((1 / 2 + num / den)) / (1 / 2 - num / den)) := by
  sorry

lemma ENNReal_final_step (num : Nat) (den : PNat) (h: 2 * num < den):
  (1/(2 : ENNReal) + num/den) / (1/2 - num/den) ≤ ENNReal.ofReal (Real.exp (Real.log ((1/2 + num/den) / (1/2 - num/den)))) := by
  have h1 : 0 < (1/2 : ℝ) - (num : ℝ)/den := by
    exact bruh1 num den h
  have h₂ : 0 < (1/2 : ℝ) + (num : ℝ)/den := by
    sorry
  have h3: ((1/2) + num/den) / (1/2 - num/den) = ENNReal.ofReal ((1/2) + (num/den : ℝ)) / (1/2 - num/den) := by sorry
  -- simp_rw [ENNReal.ofReal_sub, ENNReal.ofReal_div]
  sorry

-/
/-
lemma cat (num : ℕ) (den : ℕ+) : (0 : ℝ) < ↑↑den + 2 * num := by
  have den_pos : 0 < (den : ℕ) := den.property
  have den_real_pos : (0 : ℝ) < ↑(den : ℕ) := Nat.cast_pos.mpr den_pos
  have two_num_nonneg : 0 ≤ (2 * num : ℝ) := by
    refine mul_nonneg ?_ (Nat.cast_nonneg num)
    norm_num
  exact add_pos_of_pos_of_nonneg den_real_pos two_num_nonneg

lemma dog (num : ℕ) (den : PNat) (h : 2 * num < den) : (0 : ℝ) < ↑↑den - 2 * ↑num := by
  rw [sub_pos]
  norm_cast

lemma pig (num : ℕ) (den : ℕ+) (h : 2 * num < den) : (0 : ℝ) < (↑↑den + 2 * num) / (↑↑den - 2 * ↑num):= by
  rw [div_pos_iff]
  apply Or.inl
  apply And.intro
  exact cat num den
  exact dog num den h


lemma cow (num : Nat) (den : PNat) (h : 2 * num < den):
(0 : ℝ) ≤ (↑↑den + 2 * ↑num) / (↑↑den - 2 * ↑num) := by
  apply le_of_lt
  exact pig num den h


lemma step1 (num : Nat) (den : PNat) (h : 2 * num < den):
ENNReal.ofReal ((den + 2 * num) / (den - 2 * num)) = ENNReal.ofReal (Real.exp (Real.log ((den + 2 * num) / (den - 2 * num)))) := by
  congr
  rw [eq_comm]
  apply Real.exp_log
  apply div_pos
  {exact cat num den}
  {exact dog num den h}



lemma step2 (num : Nat) (den : PNat) (h : 2 * num < den):
    (↑↑den + 2 * ↑num) / (↑↑den - 2 * ↑num) = ENNReal.ofReal ((↑↑den + 2 * ↑num) / (↑↑den - 2 * ↑num)) := by
  rw [ENNReal.ofReal_div_of_pos]
  · congr
    norm_cast
  · have foo : 2 * (num : ℝ) < (den : ℕ) := by exact_mod_cast h
    exact sub_pos.mpr foo


lemma final_step_combined (num : Nat) (den: PNat) (h: 2 * num < den):
(den + (2: ENNReal) * num) / (den - (2 : ENNReal) * num) = ENNReal.ofReal (Real.exp (Real.log ((den + 2 * num) / (den - 2 * num)))) := by
  rw [← step1 num den h]
  exact step2 num den h

-\
