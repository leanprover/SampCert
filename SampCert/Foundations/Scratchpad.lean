import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open Classical Nat Finset BigOperators Real Set ENNReal

#check Summable.countable_support_ennreal

-- variable {T} [Fintype T]
-- variable {U} [Countable U]

-- def u : ℕ → ENNReal := sorry

-- theorem test2 (x : ENNReal) :
--   x * ⨆ i, u i = ⨆ i, x * u i := by
--   exact ENNReal.mul_iSup

-- def v (a : ℕ) : ℕ → ENNReal := sorry

-- theorem test3 (h1 : Monotone (v 0)) (h2 : Monotone (v 1)) :
--   (⨆ i, v 0 i) + (⨆ i, v 1 i) = ⨆ i, (v 0 i) + (v 1 i) := by
--   exact ENNReal.iSup_add_iSup_of_monotone h1 h2

-- def w (a : T) : ℕ → ENNReal := sorry

-- theorem test4 (h : ∀ a : T, Monotone (w a)) :
--   ∑ j : T, ⨆ i : ℕ, w j i = ⨆ i, ∑ j : T, w j i := by
--   exact ENNReal.finset_sum_iSup_nat h

-- theorem test5 (x : ENNReal) (h : ∀ a : T, Monotone (fun i => x * w a i)) :
--   ∑ j : T, ⨆ i : ℕ, x * w j i = ⨆ i, ∑ j : T, x * w j i := by
--   exact ENNReal.finset_sum_iSup_nat h

-- theorem test6 (h : ∀ a : T, Monotone (w a)) :
--   ∑' j : U, ⨆ i : ℕ, w j i = ⨆ i, ∑' j : U, w j i := by
--   refine (iSup_eq_of_tendsto ?hf ?_).symm
--   . sorry
--   . apply?

-- theorem testx1 (x : ENNReal) (u : ℕ → ENNReal) (h : Monotone u) :
--   Monotone (λ i => x * u i) := by
--   exact Monotone.const_mul' h x

-- theorem testx2 (u₁ u₂ : ℕ → ENNReal) (h₁ : Monotone u₁) (h₂ : Monotone u₂) :
--   Monotone (λ i => u₁ i + u₂ i) := by
--   exact Monotone.add h₁ h₂

-- theorem testx3 (u : T → ℕ → ENNReal) (h : forall a : T , Monotone (u a)) :
--   Monotone (λ i => ∑ a : T, u a i) := by
--   apply?

-- theorem testy1 (u : ℕ → ENNReal) (v : ENNReal) (k : ENNReal) (_ : k ≠ ⊤) (h : Filter.Tendsto u Filter.atTop (nhds v)) :
--   Filter.Tendsto (λ i => k * u i) Filter.atTop (nhds (k * v)) := by
--   refine ENNReal.Tendsto.const_mul h ?hb
--   right
--   trivial

-- #check Summable.countable_support

-- #check @tsum_subtype_add_tsum_subtype_compl ℝ ℕ
-- #check sum_add_tsum_subtype_compl

-- def split_sum (u : ℕ → ℝ) (h : Summable u) :=
--   tsum_subtype_add_tsum_subtype_compl h (setOf λ i : ℕ => True)

-- theorem sumsum (p : PMF ℕ) (k : ENNReal) :
--   ∑' (a : ℕ), p a * k = k := by
--   simp [ENNReal.tsum_mul_right]

-- theorem foo (cond : ℕ → Bool) (f : ℕ → ℝ) :
--   (∑' x : { x : ℕ // cond x }, f x)
--   =
--   1 := by
--   apply?

-- theorem split_Sum (cond : ℕ → Bool) (u₁ u₂ : ℕ → ENNReal) :
--   (∑' i : ℕ, if cond i then (u₁ i) else (u₂ i)) =
--   (∑' i : {i : ℕ // cond i}, u₁ i) + (∑' i : {i : ℕ // ¬ cond i}, u₂ i) := by
--   apply?


-- theorem test5 (x : ENNReal) :
--   ∑' a : ℕ, x * ⨆ i, v a i = ⨆ i, ∑' a : ℕ, x * v a i := by
--   sorry

  -- refine (iSup_eq_of_tendsto ?hf ?_).symm
  -- .sorry -- monotone
  -- . apply?

-- #check Summable.hasSum

-- theorem fffff (f : ℕ → ENNReal) (h : (∑' a : ℕ, f a) = 1) :
--   HasSum f 1 := by
--   have A : Summable f := by exact ENNReal.summable
--   have B := Summable.hasSum A
--   rw [h] at B
--   trivial

-- theorem nat_sub_nez (n : ℕ) (h : ¬ n = 0) :
--   (n - 1) + 1 = n := by
--   exact succ_pred h

example (a b : NNReal) (h : a + b = 1) :
  1 - a = b := by
  exact tsub_eq_of_eq_add_rev (id h.symm)

example (a b : ENNReal) (h1 : a + b = 1) (h2 : a ≠ ⊤) (h3 : b ≠ ⊤) :
  1 - a = b := by
  exact ENNReal.sub_eq_of_eq_add_rev h2 (id h1.symm)

example (f : ℕ → ENNReal) :
  (∑' (x : ↑{i | decide (↑n ≤ i) = true}ᶜ), f ↑x)
    = ∑' (x : ↑{i | decide (↑n ≤ i) = false}), f ↑x := by
  exact?

example (a b : ENNReal) (h1 : a > b) (h2 : a ≤ b) :
  False := by
  have A : a > b ↔ ¬ a ≤ b := by exact lt_iff_not_le
  rw [A] at h1
  contradiction
