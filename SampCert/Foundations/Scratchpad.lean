import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Order.Filter.AtTopBot

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

-- example (a b : NNReal) (h : a + b = 1) :
--   1 - a = b := by
--   exact tsub_eq_of_eq_add_rev (id h.symm)

-- example (a b : ENNReal) (h1 : a + b = 1) (h2 : a ≠ ⊤) (h3 : b ≠ ⊤) :
--   1 - a = b := by
--   exact ENNReal.sub_eq_of_eq_add_rev h2 (id h1.symm)

-- example (f : ℕ → ENNReal) :
--   (∑' (x : ↑{i | decide (↑n ≤ i) = true}ᶜ), f ↑x)
--     = ∑' (x : ↑{i | decide (↑n ≤ i) = false}), f ↑x := by
--   exact?

-- example (a b : ENNReal) (h1 : a > b) (h2 : a ≤ b) :
--   False := by
--   have A : a > b ↔ ¬ a ≤ b := by exact lt_iff_not_le
--   rw [A] at h1
--   contradiction

-- example :
--   ∏ i in range 0, (i + 1) = 1 := by
--   simp

-- example :
--   ∏ i in range 1, (i + 1) = 1 := by
--   simp

-- example :
--   ∏ i in range 2, (i + 1) = 2 := by
--   simp

-- example :
--   ∏ i in range 3, (i + 1) = 3! := by
--   simp

-- example (n : ℕ) :
--   ∏ i in range n, (i + 1) = n ! := by
--   simp

-- example (a x y b : ENNReal) (h : x = y) :
--   a * x * b = a * y * b := by
--   apply congrFun (congrArg HMul.hMul (congrArg (HMul.hMul _) _)) _
--   exact h

noncomputable def mass' (γ : ℝ) (n : ℕ) : ℝ := (γ^n * (n ! : ℝ)⁻¹)

-- theorem series_step_5 (γ : ℝ) (h : Summable (mass' (- γ))) :
--   (∑' (n : ℕ), (mass' (- γ) n))
--     = Real.exp (- γ) := by
--   unfold mass' at *
--   unfold Real.exp
--   unfold Complex.exp
--   unfold Complex.exp'
--   rw [tsum_def]
--   simp [h]
--   split
--   . rename_i h' -- not finite
--     sorry
--   . rename_i h'
--     unfold CauSeq.lim
--     sorry

-- example (a b c : ENNReal) :
--   a * (b + c) = a * b + a * c := by
--   exact mul_add a b c

-- example (a b c : ENNReal) :
--   a * (b - c) = a * b - a * c := by
--   rw [ENNReal.mul_sub]
--   intro h1 h2

-- example (γ : ENNReal) (h : γ < ⊤) : γ ≠ ⊤ := by exact LT.lt.ne_top h

-- #check NormedSpace.exp_eq_tsum
-- #check NormedSpace.exp_eq_tsum_div
-- #check Real.exp_eq_exp_ℝ

-- #check tsum_eq_tsum_of_ne_zero_bij
-- #check Function.Injective.tsum_eq

-- example (f : ℕ → ENNReal) :
--   (∑' i : ℕ, (f (2 * i) + f (2 * i + 1)))
--     = ∑' i : ℕ, f i := by
--   refine tsum_eq_tsum_of_ne_zero_bij ?i (fun ⦃a₁⦄ => ?_) ?hf ?hfg

-- example (f : ℕ → ℝ) (h : Summable f):
--   (∑' i : ℕ, (f (2 * i) + f (2 * i + 1)))
--     = ∑' i : ℕ, f i := by
--   refine (tsum_eq_tsum_of_hasSum_iff_hasSum ?h).symm

-- example (f g : ℕ → ENNReal) :
--   (∑' n : ℕ, (f n + g n)) = (∑' n : ℕ, f n) + (∑' n : ℕ, g n) := by
--   exact ENNReal.tsum_add

-- #check ENNReal.tsum_add
-- #check ENNReal.tsum_sub

-- example (f g : ℕ → ENNReal) (h1 : ∀ n : ℕ, g n = f (n + 1)):
--   (∑' n : ℕ, (f n - g n)) = (∑' n : ℕ, f n) - (∑' n : ℕ, g n) := by
--   rw [ENNReal.tsum_sub]

-- theorem foo (f : ℕ → ENNReal) (i : ℕ) :
--   (∑ n in range (i + 1), if n = 0 then 0 else f (n-1))
--     = (∑ n in range i, f n) := by
--   induction i
--   . simp
--   . rename_i i IH
--     rw [sum_range_succ]
--     simp
--     conv =>
--       right
--       rw [sum_range_succ]
--     rw [← IH]

-- @[simp]
-- theorem foo (f : ℕ → ℝ) (i : ℕ) :
--   (∑ n in range (i + 1), (f n - f (n + 1))) = f 0 - f (i + 1) := by
--   induction i
--   . simp
--   . rename_i n IH
--     rw [sum_range_succ]
--     rw [IH]
--     rw [sub_add_sub_cancel]


-- @[simp]
-- theorem bar :
--   Filter.Tendsto plop Filter.atTop (nhds 0) := by
--   sorry

-- theorem tsum_cancel (f : ℕ → ℝ) :
--   (∑' (n : ℕ), (f n - f (n + 1))) = f 0 := by
--   rw [HasSum.tsum_eq]
--   sorry


-- theorem tsum_cancel' (f : ℕ → ENNReal) :
--   (∑' (n : ℕ), (f n - f (n + 1))) = f 0 := by
--   rw [ENNReal.tsum_eq_iSup_nat]
--   sorry

noncomputable def plop0 (n : ℕ) (γ : ENNReal) := (γ^(n - 2) * (((n - 2)!) : ENNReal)⁻¹) * (1 - (γ * ((n : ENNReal) - 1)⁻¹))
noncomputable def plop1 (n : ℕ) (γ : ENNReal) := (γ^n * (((n)!) : ENNReal)⁻¹)
noncomputable def plop2 (n : ℕ) (γ : ℝ) := (γ^n * (((n)!) : ℝ)⁻¹)

theorem foo (i : ℕ) (γ : ℝ) :
  (∑ n in range i, (plop2 (2 * n) γ - plop2 (2 * n + 1) γ))
    = (∑ n in range (2 * i), plop2 n (- γ)) := by
  induction i
  . simp
  . rename_i i IH
    rw [sum_range_succ]
    have A : 2 * succ i = succ (succ ( 2 * i)) := rfl
    rw [A]
    rw [sum_range_succ]
    rw [sum_range_succ]
    rw [IH]
    rw [add_assoc]
    congr
    unfold plop2
    simp
    rw [← Mathlib.Tactic.RingNF.add_neg]
    congr
    rw [neg_mul_eq_neg_mul]
    congr
    rw [Odd.neg_pow (Exists.intro i rfl) γ]

#check Filter.tendsto_add_atTop_iff_nat

namespace Filter

theorem tendsto_add_atTop_iff_natddd {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Filter.Tendsto (fun n => f (n + k)) atTop l ↔ Filter.Tendsto f atTop l :=
  show Filter.Tendsto (f ∘ fun n => n + k) atTop l ↔ Filter.Tendsto f atTop l by
    rw [← Filter.tendsto_map'_iff, Filter.map_add_atTop_eq_nat]

theorem map_mul_atTop_eq_nat : map (fun a => 2 * a) atTop = atTop := by
  sorry

  -- map_atTop_eq_of_gc (fun a => a - a) a (fun a b h => add_le_add_right h a)
  --   (fun a b h => (le_tsub_iff_right h).symm) fun a h => by rw [tsub_add_cancel_of_le h]

theorem tendsto_mul_atTop_iff_nat {f : ℕ → α} {l : Filter α} :
    Filter.Tendsto (fun n => f (2 * n)) atTop l ↔ Filter.Tendsto f atTop l :=
  show Filter.Tendsto (f ∘ fun n => 2 * n) atTop l ↔ Filter.Tendsto f atTop l by
    rw [← Filter.tendsto_map'_iff, map_mul_atTop_eq_nat]


end Filter

example (γ : ℝ) :
  (∑' n : ℕ, (plop2 (2 * n) γ - plop2 (2 * n + 1) γ))
    = ∑' n : ℕ, plop2 n (- γ) := by
  refine (tsum_eq_tsum_of_hasSum_iff_hasSum ?h).symm
  intro a
  rw [Summable.hasSum_iff_tendsto_nat]
  . rw [Summable.hasSum_iff_tendsto_nat]
    . conv =>
        right
        congr
        . intro n
          rw [foo]
        . skip
        . skip
      -- like the following, but multiplying
      -- rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
      sorry
    . sorry
  . sorry


theorem bar (i : ℕ) (γ : ENNReal) (h : γ ≠ ⊤) :
  ∑ a in Finset.range i, (plop1 (2 * a) γ - plop1 (2 * a + 1) γ) =
  ∑ a in Finset.range (2 * i), ENNReal.ofReal (plop2 a (-ENNReal.toReal γ)) := by
  rw [← @ENNReal.ofReal_toReal (∑ a in Finset.range i, (plop1 (2 * a) γ - plop1 (2 * a + 1) γ))]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  congr
  rw [ENNReal.toReal_sum]
  have X : ∀ a : ℕ, plop1 (2 * a + 1) γ ≤ plop1 (2 * a) γ := sorry
  have Y : ∀ a : ℕ, plop1 (2 * a) γ ≠ ⊤ := sorry
  conv =>
    left
    right
    intro a
    rw [ENNReal.toReal_sub_of_le (X a) (Y a)]
  unfold plop1
  conv =>
    left
    right
    intro a
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv]
    rw [toReal_nat]
    rw [toReal_nat]
  unfold plop2
  clear X Y
  induction i
  . simp
  . rename_i i IH
    rw [sum_range_succ]
    have A : 2 * succ i = succ (succ ( 2 * i)) := rfl
    rw [A]
    rw [sum_range_succ]
    rw [sum_range_succ]
    rw [IH]
    rw [add_assoc]
    congr
    simp
    rw [← Mathlib.Tactic.RingNF.add_neg]
    congr
    rw [neg_mul_eq_neg_mul]
    congr
    exact (Odd.neg_pow (Exists.intro i rfl) (ENNReal.toReal γ)).symm

theorem Monotone.iSup_nat_mul {f : ℕ → ENNReal} (hf : Monotone f) : ⨆ n, f (2 * n) = ⨆ n, f n :=
  le_antisymm (iSup_le fun i => le_iSup _ (2 * i)) <| iSup_mono fun i => hf <| Nat.le_mul_of_pos_left i (le.step le.refl)


-- rw plop2 with foo so that every term becomes positive?
-- theorem foobar (γ : ENNReal) (h : γ ≠ ⊤) :
--   (∑' n : ℕ, (plop1 (2 * n) γ - plop1 (2 * n + 1) γ))
--     = ENNReal.ofReal (∑' n : ℕ, plop2 n (- γ.toReal)) := by
--   rw [ENNReal.tsum_eq_iSup_nat]
--   rw [ENNReal.ofReal_tsum_of_nonneg]
--   . rw [ENNReal.tsum_eq_iSup_nat]
--     have X : Monotone fun i => ∑ a in Finset.range i, (ENNReal.ofReal (plop2 a (-ENNReal.toReal γ))) := sorry
--     conv =>
--       right
--       rw [← Monotone.iSup_nat_mul X]
--     rw [iSup_congr]
--     intro i
--     rw [bar _ _ h]
--   . intro n
--     unfold plop2
--     sorry -- that's not true
--   . sorry

example (a b : ENNReal) (h1 : a ≥ b) (h2 : a ≠ ⊤) :
  ENNReal.toReal (a - b) = ENNReal.toReal a - ENNReal.toReal b := by
  exact toReal_sub_of_le h1 h2

example (γ : ENNReal) :
  ∑' (k : ℕ), (-ENNReal.toReal γ) ^ (2 * k + 1)
    = - ∑' (k : ℕ), (ENNReal.toReal γ) ^ (2 * k + 1) := by
  rw [← tsum_neg]
  sorry


theorem foobar (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' n : ℕ, (plop1 (2 * n) γ - plop1 (2 * n + 1) γ))
    = ENNReal.ofReal (∑' n : ℕ, plop2 n (- γ.toReal)) := by
  rw [← @ENNReal.ofReal_toReal (∑' (n : ℕ), (plop1 (2 * n) γ - plop1 (2 * n + 1) γ))]
  rw [ENNReal.tsum_sub]
  rw [toReal_sub_of_le]
  rw [tsum_toReal_eq]
  rw [tsum_toReal_eq]
  unfold plop1
  conv =>
    left
    right
    left
    right
    intro a
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv]
  conv =>
    left
    right
    right
    right
    intro a
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv]
  simp

  conv =>
    right
    rw [← tsum_even_add_odd sorry sorry]

  unfold plop2
  simp

  congr




theorem series_step_4 (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (n : ℕ), (plop1 (2 * n) γ - plop1 (2 * n + 1) γ))
    = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  rw [foobar _ h]
  congr
  unfold plop2
  rw [Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum_div]
  simp
  congr




  -- rw [← @ENNReal.ofReal_toReal (∑' (n : ℕ), (plop1 (2 * n) γ - plop1 (2 * n + 1) γ))]
  -- congr
  -- rw [ENNReal.tsum_toReal_eq]
  -- rw [HasSum.tsum_eq]
  -- rw [Summable.hasSum_iff_tendsto_nat]
  -- sorry
  -- sorry
  -- sorry
  -- sorry

-- theorem series_step_4' (γ : ENNReal) :
--   (∑' (n : ℕ), (plop1 (2 * n) γ - plop1 (2 * n + 1) γ))
--     = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
--   rw [ENNReal.tsum_eq_iSup_nat]




-- example (γ : ENNReal) :
--   (∑' n : ℕ, (plop1 (2 * n) γ - plop1 (2 * n + 1) γ)).toReal
--     = (∑' n : ℕ, plop2 n (- γ.toReal)) := by
--   unfold plop1
--   unfold plop2
--   rw [ENNReal.tsum_sub]
--   . rw [ENNReal.toReal_sub_of_le]
--     . rw [ENNReal.tsum_toReal_eq]
--       . rw [ENNReal.tsum_toReal_eq]
--         . conv =>
--             left
--             left
--             right
--             intro a
--             rw [ENNReal.toReal_mul]
--             rw [ENNReal.toReal_pow]
--             rw [ENNReal.toReal_inv]
--           conv =>
--             left
--             right
--             right
--             intro a
--             rw [ENNReal.toReal_mul]
--             rw [ENNReal.toReal_pow]
--             rw [ENNReal.toReal_inv]
--           simp
--           rw [← _root_.tsum_sub]
--           sorry
--         . sorry
--       . sorry
--     . sorry
--     . sorry
--   . sorry
--   . sorry


  -- rw [Real.exp_eq_exp_ℝ]
  -- rw [NormedSpace.exp_eq_tsum_div]
  -- simp [mass']
  -- rw [ENNReal.ofReal_tsum_of_nonneg]
  -- . sorry
  -- . intro n
  --   induction n
  --   . simp
  --   . sorry
  -- . sorry


example (f g : ℕ → ENNReal) (h : ∀ x, f x ≤ g x) :
  (∑' n : ℕ, f x) ≤ (∑' n : ℕ, g x) := by
  exact ENNReal.tsum_le_tsum fun a => h x

example (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ ⊤) :
  a - b ≠ ⊤ := by
  exact ENNReal.sub_ne_top h1
