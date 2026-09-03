/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.Selector

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
PMF bridge lemmas connecting permutation averages to the paper closed form.

Guide:
- the first block proves derivative and monotonicity facts for the paper polynomials;
- the middle block expands permutation products into subset sums;
- the final block identifies the actual PMF with the paper closed form.
-/

/-! ### Analytic facts about the paper polynomial -/
theorem hasDerivAt_paperPrimitivePoly
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) :
    HasDerivAt
      (paperPrimitivePoly q r ε₁ ε₂)
      (∏ i ∈ Finset.univ.erase r, (1 - c * paperProb q ε₁ ε₂ i))
      c := by
  unfold paperPrimitivePoly
  have hsum :
      HasDerivAt
        (∑ t ∈ (Finset.univ.erase r).powerset, fun x : ℝ =>
          x ^ (t.card + 1) *
            ((((-1 : ℝ) ^ t.card) / (t.card + 1)) *
              ∏ i ∈ t, paperProb q ε₁ ε₂ i))
        (∑ t ∈ (Finset.univ.erase r).powerset,
          c ^ t.card * (((t.card + 1 : ℝ)) *
            ((((-1 : ℝ) ^ t.card) / (t.card + 1)) *
              ∏ i ∈ t, paperProb q ε₁ ε₂ i)))
        c := by
          exact
            (HasDerivAt.sum
              (u := Finset.powerset (Finset.univ.erase r))
              (A := fun t => fun x : ℝ =>
                x ^ (t.card + 1) *
                  ((((-1 : ℝ) ^ t.card) / (t.card + 1)) *
                    ∏ i ∈ t, paperProb q ε₁ ε₂ i))
              (A' := fun t =>
                c ^ t.card * (((t.card + 1 : ℝ)) *
                  ((((-1 : ℝ) ^ t.card) / (t.card + 1)) *
                    ∏ i ∈ t, paperProb q ε₁ ε₂ i)))
              (x := c)
              (fun t _ht => by
                have hpow : HasDerivAt (fun x : ℝ => x ^ (t.card + 1)) ((t.card + 1 : ℝ) * c ^ t.card) c := by
                  simpa using hasDerivAt_pow (t.card + 1) c
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  hpow.const_mul
                    (((( -1 : ℝ) ^ t.card) / (t.card + 1)) * ∏ i ∈ t, paperProb q ε₁ ε₂ i)))
  have hderivEq :
      (∑ t ∈ (Finset.univ.erase r).powerset,
        (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ((t.card + 1 : ℝ) * c ^ t.card) *
          ∏ i ∈ t, paperProb q ε₁ ε₂ i)
        =
      ∏ i ∈ Finset.univ.erase r, (1 - c * paperProb q ε₁ ε₂ i) := by
        -- This is the key algebraic step in the paper's analytic argument:
        -- differentiate the alternating subset sum termwise, then recognize the
        -- resulting sum as the product expansion of `∏ (1 - c * p_i)`.
        calc
          ∑ t ∈ (Finset.univ.erase r).powerset,
              (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ((t.card + 1 : ℝ) * c ^ t.card) *
                ∏ i ∈ t, paperProb q ε₁ ε₂ i
            = ∑ t ∈ (Finset.univ.erase r).powerset,
                (((-1 : ℝ) ^ t.card) * (c ^ t.card)) * ∏ i ∈ t, paperProb q ε₁ ε₂ i := by
                  apply Finset.sum_congr rfl
                  intro t _ht
                  have hne : ((t.card : ℝ) + 1) ≠ 0 := by positivity
                  field_simp [hne]
                  -- ring
          _ = ∑ t ∈ (Finset.univ.erase r).powerset,
                ∏ i ∈ t, (-(c * paperProb q ε₁ ε₂ i)) := by
                  apply Finset.sum_congr rfl
                  intro t _ht
                  have hpowneg : ((-c : ℝ) ^ t.card) = ((-1 : ℝ) ^ t.card) * c ^ t.card := by
                    rw [neg_eq_neg_one_mul, mul_pow]
                  calc
                    (((-1 : ℝ) ^ t.card) * (c ^ t.card)) * ∏ i ∈ t, paperProb q ε₁ ε₂ i
                      = ((-c : ℝ) ^ t.card) * ∏ i ∈ t, paperProb q ε₁ ε₂ i := by
                          rw [hpowneg]
                    _ = (∏ _i ∈ t, (-c : ℝ)) * ∏ i ∈ t, paperProb q ε₁ ε₂ i := by
                          rw [Finset.prod_const]
                    _ = ∏ i ∈ t, ((-c : ℝ) * paperProb q ε₁ ε₂ i) := by
                          rw [← Finset.prod_mul_distrib]
                    _ = ∏ i ∈ t, (-(c * paperProb q ε₁ ε₂ i)) := by
                          apply Finset.prod_congr rfl
                          intro i _hi
                          ring
          _ = ∏ i ∈ Finset.univ.erase r, (1 - c * paperProb q ε₁ ε₂ i) := by
                exact sum_powerset_neg_prod_eq_prod_one_sub (Finset.univ.erase r) (fun i => c * paperProb q ε₁ ε₂ i)
  convert hsum using 1
  · ext x
    simp [mul_assoc, mul_comm]
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hderivEq.symm

theorem paperPrimitivePoly_monotoneOn_Icc
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    MonotoneOn (paperPrimitivePoly q r ε₁ ε₂) (Set.Icc (0 : ℝ) 1) := by
  have hdiff : Differentiable ℝ (paperPrimitivePoly q r ε₁ ε₂) := by
    intro x
    exact (hasDerivAt_paperPrimitivePoly q r ε₁ ε₂ x).differentiableAt
  -- The derivative is a product of terms `1 - c * p_i`, and on `c ∈ [0,1]`
  -- each factor stays nonnegative because every paper probability `p_i` also
  -- lies in `[0,1]`.
  refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rcases hx with ⟨hx0, hx1⟩
  rw [(hasDerivAt_paperPrimitivePoly q r ε₁ ε₂ x).deriv]
  apply Finset.prod_nonneg
  intro i _hi
  have hpi0 : 0 ≤ paperProb q ε₁ ε₂ i := paperProb_nonneg q ε₁ ε₂ i
  have hpi1 : paperProb q ε₁ ε₂ i ≤ 1 := paperProb_le_one q ε₁ ε₂ i
  have hmul : 0 ≤ x * paperProb q ε₁ ε₂ i ∧ x * paperProb q ε₁ ε₂ i ≤ 1 := by
    constructor
    · exact mul_nonneg hx0.le hpi0
    · have : x ≤ 1 := hx1.le
      nlinarith
  linarith

theorem paperAltScaled_mul_le_paperAlt
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c * paperAltScaled q r ε₁ ε₂ c ≤ paperAlt q r ε₁ ε₂ := by
  have hmono := paperPrimitivePoly_monotoneOn_Icc q r ε₁ ε₂
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc0, hc1⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hle := hmono hc h1 hc1
  have hle' : paperPrimitiveScaled q r ε₁ ε₂ c ≤ paperPrimitiveScaled q r ε₁ ε₂ 1 := by
    simpa [paperPrimitiveScaled_eq_paperPrimitivePoly] using hle
  -- `paperAltScaled` is the normalized primitive divided by `c`, so the
  -- monotonicity of the primitive gives exactly the scaled inequality we need.
  simpa [paperPrimitiveScaled, paperAltScaled_one] using hle'

/-! ### Expanding permutation events into subset sums -/

theorem beforeSet_prod_expand
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ)) (q : Scores n)
    (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i) =
      ∑ t ∈ (Finset.univ.erase r).powerset,
        if t ⊆ beforeSet σ r then ∏ i ∈ t, (-paperProb q ε₁ ε₂ i) else 0 := by
  calc
    ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)
      = ∑ t ∈ (beforeSet σ r).powerset, ∏ i ∈ t, (-paperProb q ε₁ ε₂ i) := by
          -- Expand the finite product by the standard powerset identity:
          -- each subset chooses the `-p_i` term for exactly the indices it contains.
          symm
          exact sum_powerset_neg_prod_eq_prod_one_sub (beforeSet σ r) (paperProb q ε₁ ε₂)
    _ =
        ∑ t ∈ (Finset.univ.erase r).powerset,
          if t ⊆ beforeSet σ r then ∏ i ∈ t, (-paperProb q ε₁ ε₂ i) else 0 := by
            -- Re-express the same sum over the larger ambient powerset
            -- `powerset (univ.erase r)`, with an indicator telling us whether
            -- the subset actually lies inside `beforeSet σ r`.
            exact sum_powerset_beforeSet_eq_sum_filter σ r (fun t => ∏ i ∈ t, (-paperProb q ε₁ ε₂ i))

theorem sum_perm_powerset_comm
    {n : CandidateCount} (r : Fin n.succ)
    (f : Equiv.Perm (Fin n.succ) → Finset (Fin n.succ) → ℝ) :
    ∑ σ : Equiv.Perm (Fin n.succ), ∑ t ∈ (Finset.univ.erase r).powerset, f σ t
      =
    ∑ t ∈ (Finset.univ.erase r).powerset, ∑ σ : Equiv.Perm (Fin n.succ), f σ t := by
  classical
  simpa using
    (Finset.sum_comm'
      (s := (Finset.univ : Finset (Equiv.Perm (Fin n.succ))))
      (t := fun _σ => (Finset.univ.erase r).powerset)
      (t' := (Finset.univ.erase r).powerset)
      (s' := fun _t => (Finset.univ : Finset (Equiv.Perm (Fin n.succ))))
      (f := fun σ t => f σ t)
      (by
        intro σ t
        simp))

theorem sum_beforeSet_prod_eq_sum_neg_prod_coeff
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ∑ σ : Equiv.Perm (Fin n.succ),
        (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
          ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)
      =
    ∑ t ∈ (Finset.univ.erase r).powerset,
      (((t.card + 1 : ℕ) : ℝ)⁻¹) * ∏ i ∈ t, (-paperProb q ε₁ ε₂ i) := by
  let P : Finset (Finset (Fin n.succ)) := (Finset.univ.erase r).powerset
  let G : Finset (Fin n.succ) → ℝ := fun t => ∏ i ∈ t, (-paperProb q ε₁ ε₂ i)
  calc
    ∑ σ : Equiv.Perm (Fin n.succ),
        (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
          ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)
      =
        ∑ σ : Equiv.Perm (Fin n.succ),
          ∑ t ∈ P,
            (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
              (if t ⊆ beforeSet σ r then G t else 0) := by
                apply Finset.sum_congr rfl
                intro σ _hσ
                simp [P, G, beforeSet_prod_expand σ q r ε₁ ε₂, Finset.mul_sum]
    _ =
        ∑ t ∈ P,
          ∑ σ : Equiv.Perm (Fin n.succ),
            (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
              (if t ⊆ beforeSet σ r then G t else 0) := by
                -- Swap the order of summation: first choose the subset `t`,
                -- then count how often it appears before `r` under a uniform permutation.
                simpa [P] using
                  (sum_perm_powerset_comm r
                    (fun σ t =>
                      (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
                        (if t ⊆ beforeSet σ r then G t else 0)))
    _ =
        ∑ t ∈ P,
          (∑ σ : Equiv.Perm (Fin n.succ),
            (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
              (if t ⊆ beforeSet σ r then 1 else 0)) * G t := by
                -- Now factor out the subset-dependent term `G t`; the inner sum
                -- is exactly the coefficient "probability that all of `t` occur before `r`".
                apply Finset.sum_congr rfl
                intro t _ht
                have hfactor :
                    ∑ σ : Equiv.Perm (Fin n.succ),
                      (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
                        (if t ⊆ beforeSet σ r then G t else 0)
                      =
                    ∑ σ : Equiv.Perm (Fin n.succ),
                      ((PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
                        (if t ⊆ beforeSet σ r then 1 else 0)) * G t := by
                          apply Finset.sum_congr rfl
                          intro σ _hσ
                          split <;> ring
                rw [hfactor, Finset.sum_mul]
    _ =
        ∑ t ∈ P, (((t.card + 1 : ℕ) : ℝ)⁻¹) * G t := by
          apply Finset.sum_congr rfl
          intro t ht
          have ht' : t ⊆ Finset.univ.erase r := by
            simpa [P] using (Finset.mem_powerset.mp ht)
          have hr' : r ∉ t := by
            intro h
            exact (Finset.mem_erase.mp (ht' (by simp [h]))).1 rfl
          rw [real_subset_beforeSet_coeff (r := r) (t := t) hr']
    _ = ∑ t ∈ (Finset.univ.erase r).powerset,
          (((t.card + 1 : ℕ) : ℝ)⁻¹) * ∏ i ∈ t, (-paperProb q ε₁ ε₂ i) := by
            rfl

theorem tsum_beforeSet_prod_eq_ofReal_paperAlt
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    ∑' σ : Equiv.Perm (Fin n.succ),
      PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
        ∏ i ∈ beforeSet σ r, exactCoinPMF (gap q i * ε₁) ε₂ false
      = ENNReal.ofReal (paperAlt q r ε₁ ε₂) := by
  rw [tsum_fintype]
  calc
    ∑ σ : Equiv.Perm (Fin n.succ),
        PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
          ∏ i ∈ beforeSet σ r, exactCoinPMF (gap q i * ε₁) ε₂ false
      =
        ∑ σ : Equiv.Perm (Fin n.succ),
          ENNReal.ofReal
            ((PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
              ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)) := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            have hprod :
                ∏ i ∈ beforeSet σ r, exactCoinPMF (gap q i * ε₁) ε₂ false =
                  ENNReal.ofReal (∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)) := by
              calc
                ∏ i ∈ beforeSet σ r, exactCoinPMF (gap q i * ε₁) ε₂ false
                  = ∏ i ∈ beforeSet σ r, ENNReal.ofReal (1 - paperProb q ε₁ ε₂ i) := by
                      apply Finset.prod_congr rfl
                      intro i _hi
                      exact (ofReal_one_sub_paperProb_eq_exactCoin_false q ε₁ ε₂ i).symm
                _ = ENNReal.ofReal (∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)) := by
                      symm
                      apply ENNReal.ofReal_prod_of_nonneg
                      intro i _hi
                      have hle := paperProb_le_one q ε₁ ε₂ i
                      exact sub_nonneg.mpr hle
            calc
              PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
                  ∏ i ∈ beforeSet σ r, exactCoinPMF (gap q i * ε₁) ε₂ false
                = ENNReal.ofReal ((PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal) *
                    ENNReal.ofReal (∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)) := by
                      rw [ENNReal.ofReal_toReal]
                      · rw [hprod]
                      · simp
              _ =
                  ENNReal.ofReal
                    ((PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
                      ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)) := by
                        rw [← ENNReal.ofReal_mul]
                        exact ENNReal.toReal_nonneg
    _ =
        ENNReal.ofReal
          (∑ σ : Equiv.Perm (Fin n.succ),
            (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ).toReal *
              ∏ i ∈ beforeSet σ r, (1 - paperProb q ε₁ ε₂ i)) := by
                -- Convert the finite ENNReal average into an ordinary real-valued
                -- sum, where the counting lemmas can be applied directly.
                symm
                apply ENNReal.ofReal_sum_of_nonneg
                intro σ _hσ
                apply mul_nonneg
                · exact ENNReal.toReal_nonneg
                · exact Finset.prod_nonneg (fun i _hi => by
                    have hle := paperProb_le_one q ε₁ ε₂ i
                    exact sub_nonneg.mpr hle)
    _ = ENNReal.ofReal (paperAlt q r ε₁ ε₂) := by
          -- The remaining step is a direct substitution: the finite
          -- real-valued sum is exactly the coefficient formula proved earlier,
          -- and that formula is how `paperAlt` was defined.
          rw [sum_beforeSet_prod_eq_sum_neg_prod_coeff, paperAlt_eq_sum_neg_prod]

/--
This is the main closed-form bridge to the paper: the PMF of output `r`
matches the paper's real-valued expression `paperProb * paperAlt`.

It packages the supplement's closed-form derivation used in the
proof of Theorem 1.
-/
theorem permuteAndFlipPMF_eq_exactCoin_mul_ofReal_paperAlt
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    permuteAndFlipPMF n q ε₁ ε₂ r =
      exactCoinPMF (gap q r * ε₁) ε₂ true * ENNReal.ofReal (paperAlt q r ε₁ ε₂) := by
  rw [permuteAndFlipPMF_eq_coin_mul_tsum_beforeSet_prod]
  rw [tsum_beforeSet_prod_eq_ofReal_paperAlt]

theorem permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    permuteAndFlipPMF n q ε₁ ε₂ r =
      ENNReal.ofReal (paperProb q ε₁ ε₂ r * paperAlt q r ε₁ ε₂) := by
  rw [permuteAndFlipPMF_eq_exactCoin_mul_ofReal_paperAlt]
  rw [exactCoinPMF_apply_true, paperProb]
  rw [← ENNReal.ofReal_mul]
  · positivity

theorem permuteAndFlipPMF_max_eq_ofReal_paperAlt
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ)
    (hgap : gap q r = 0) :
    permuteAndFlipPMF n q ε₁ ε₂ r = ENNReal.ofReal (paperAlt q r ε₁ ε₂) := by
  rw [permuteAndFlipPMF_eq_exactCoin_mul_ofReal_paperAlt]
  simp [hgap]

theorem permuteAndFlipPMF_bumpScore_self_one_of_gap_zero_eq_ofReal_paperAltScaled
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hgap : gap q r = 0) :
    permuteAndFlipPMF n (bumpScore q r 1) ε₁ ε₂ r =
      ENNReal.ofReal
        (paperAltScaled q r ε₁ ε₂ (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)))) := by
  have hgap' : gap (bumpScore q r 1) r = 0 := by
    have hmax : maxScore q ≤ q r + 1 := by
      rw [maxScore_eq_of_gap_zero q r hgap]
      omega
    simpa using gap_bumpScore_self_of_ge q r 1 hmax
  rw [permuteAndFlipPMF_max_eq_ofReal_paperAlt n (bumpScore q r 1) ε₁ ε₂ r hgap']
  rw [paperAlt_bumpScore_self_one_of_gap_zero q r ε₁ ε₂ hgap]

theorem permuteAndFlipPMF_bumpScore_self_one_of_gap_zero
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hgap : gap q r = 0) :
    ENNReal.ofReal (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) *
        permuteAndFlipPMF n (bumpScore q r 1) ε₁ ε₂ r ≤
      permuteAndFlipPMF n q ε₁ ε₂ r := by
  -- Once `r` is already maximal, both PMFs can be rewritten entirely in the
  -- paper's closed form, and the inequality reduces to the scalar monotonicity
  -- statement `paperAltScaled_mul_le_paperAlt`.
  rw [permuteAndFlipPMF_bumpScore_self_one_of_gap_zero_eq_ofReal_paperAltScaled q r ε₁ ε₂ hgap]
  rw [permuteAndFlipPMF_max_eq_ofReal_paperAlt n q ε₁ ε₂ r hgap]
  rw [← ENNReal.ofReal_mul]
  · apply ENNReal.ofReal_le_ofReal
    have hρ0 : 0 ≤ Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) := by
      positivity
    have hρ1 : Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)) ≤ 1 := by
      have hnonneg : (0 : ℝ) ≤ (((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) := by positivity
      have hle0 : -((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) ≤ 0 := by
        linarith
      have hle : Real.exp (-((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) ≤ Real.exp 0 := by
        exact Real.exp_le_exp.mpr hle0
      convert hle using 1
      simp
    exact paperAltScaled_mul_le_paperAlt q r ε₁ ε₂ hρ0 hρ1
  · positivity

end PermuteAndFlip
end SLang
