
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open Classical PMF Nat Finset BigOperators

@[simp]
def u₁ (n : ℕ) : ℝ := (1/2)^n
@[simp]
def u₂ (n : ℕ) : ENNReal := (1/2)^n

@[simp]
def s₁ (n : ℕ) := ∑ m in range n, u₁ m
@[simp]
def s₂ (n : ℕ) := ∑ m in range n, u₂ m

theorem s_eq : ⨆ n, s₁ n =  ENNReal.toReal (⨆ n, s₂ n) := by
  rw [ENNReal.toReal_iSup]
  . apply iSup_congr
    intro i
    simp [s₁, s₂]
    induction i
    . simp
    . rename_i n IH
      rw [geom_sum_succ]
      rw [mul_sum]
      rw [ENNReal.toReal_add]
      . rw [(mul_sum (range n) (fun i => 2⁻¹ ^ i) 2⁻¹).symm]
        rw [ENNReal.toReal_mul]
        rw [← IH]
        clear IH
        simp
        rw [sum_range_succ_comm]
        sorry -- looks good
      . sorry -- looks good
      . simp
  . sorry -- looks good
