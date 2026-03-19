/-
Copyright (c) 2026 Michael Shoemate.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.Core

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
Paper polynomial and analytic lemmas for the paper-style proof.
-/

/-! ### The paper's real-valued quantities -/

theorem sum_powerset_neg_prod_eq_prod_one_sub
    {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    ∑ t in s.powerset, ∏ i in t, (-f i) = ∏ i in s, (1 - f i) := by
  simpa [sub_eq_add_neg, add_comm] using
    (Finset.prod_add (f := fun i => -f i) (g := fun _ => (1 : ℝ)) s).symm

/--
The paper's `p_i` term: the exact Bernoulli acceptance probability for
candidate `i`, viewed in `ℝ` rather than `ENNReal`.
-/
def paperProb {n : CandidateCount} (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (i : Fin n.succ) : ℝ :=
  Real.exp (- (((gap q i * ε₁ : ℕ) : NNReal) / ε₂))

/--
The paper's alternating subset sum `A_r(q)`. Later modules show that this is
exactly the PMF mass on `r`, after factoring out the direct success term for `r`.
-/
def paperAlt {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) : ℝ :=
  ∑ t in (Finset.univ.erase r).powerset,
    (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ∏ i in t, paperProb q ε₁ ε₂ i

/-- The scaled version of `paperAlt`, used when all non-`r` terms are multiplied by a common factor. -/
def paperAltScaled {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) : ℝ :=
  ∑ t in (Finset.univ.erase r).powerset,
    (((-1 : ℝ) ^ t.card) / (t.card + 1)) * (c ^ t.card) * ∏ i in t, paperProb q ε₁ ε₂ i

/--
The paper primitive `c ↦ c * paperAltScaled ... c`.

This is the analytic object whose derivative becomes a clean product
`∏ (1 - c * p_i)`, making monotonicity easy to prove on `[0,1]`.
-/
def paperPrimitiveScaled {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) : ℝ :=
  c * paperAltScaled q r ε₁ ε₂ c

/--
Reduced alternating sum for the gap-zero / maximizer case with one distinguished
extra candidate `s` removed.

This is the polynomial that appears after splitting `paperAlt` into subsets that
do or do not contain a candidate with gap `0`.
-/
def paperAltGapZeroScaled {n : CandidateCount}
    (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) : ℝ :=
  ∑ t in ((Finset.univ.erase r).erase s).powerset,
    (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
      (c ^ t.card) * ∏ i in t, paperProb q ε₁ ε₂ i

/--
An antiderivative-like helper for `paperAltGapZeroScaled`.

The extra factor `c^2` is chosen so that differentiating twice exposes the same
product structure as in the main paper polynomial argument.
-/
def paperGapZeroDoublePrimitive {n : CandidateCount}
    (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) : ℝ :=
  c ^ 2 * paperAltGapZeroScaled q r s ε₁ ε₂ c

/--
The first derivative of `paperGapZeroDoublePrimitive`, written explicitly as a
finite sum.
-/
def paperGapZeroPrimitive {n : CandidateCount}
    (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) : ℝ :=
  ∑ t in ((Finset.univ.erase r).erase s).powerset,
    (((-1 : ℝ) ^ t.card) / (t.card + 1)) *
      (c ^ (t.card + 1)) * ∏ i in t, paperProb q ε₁ ε₂ i

theorem paperAltScaled_one
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    paperAltScaled q r ε₁ ε₂ 1 = paperAlt q r ε₁ ε₂ := by
  unfold paperAltScaled paperAlt
  apply Finset.sum_congr rfl
  intro t _ht
  simp

/-! ### Simplifying the maximizer case -/

theorem paperAlt_eq_sum_erase_gap_zero
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : s ≠ r) (hs : gap q s = 0) :
    paperAlt q r ε₁ ε₂ =
      ∑ t in ((Finset.univ.erase r).erase s).powerset,
        (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
          ∏ i in t, paperProb q ε₁ ε₂ i := by
  have hs_not_mem : s ∉ (Finset.univ.erase r).erase s := by simp
  have hsplit :
      (Finset.univ.erase r).powerset =
        (((Finset.univ.erase r).erase s).powerset) ∪
          ((((Finset.univ.erase r).erase s).powerset).image (insert s)) := by
    -- Split all subsets into those that omit `s` and those that contain it.
    rw [← Finset.powerset_insert]
    congr
    ext x
    simp [hrs]
  rw [paperAlt, hsplit, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hts : s ∉ t := by
        intro hst
        exact hs_not_mem ((Finset.mem_powerset.mp ht) hst)
      have hcard : (insert s t).card = t.card + 1 := Finset.card_insert_of_not_mem hts
      have hprod :
          ∏ i in insert s t, paperProb q ε₁ ε₂ i =
            ∏ i in t, paperProb q ε₁ ε₂ i := by
        rw [Finset.prod_insert hts]
        unfold paperProb
        simp [hs]
      have hcoeff :
          ((((-1 : ℝ) ^ t.card) / (t.card + 1)) +
              (((-1 : ℝ) ^ (t.card + 1)) / (t.card + 2))) =
            (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) := by
          -- Pair the "without `s`" and "with `s`" coefficients into the single
          -- reduced coefficient used by `paperAltGapZeroScaled`.
          have hne1 : ((t.card : ℝ) + 1) ≠ 0 := by positivity
          have hne2 : ((t.card : ℝ) + 2) ≠ 0 := by positivity
          field_simp [hne1, hne2]
          ring
      calc
        (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ∏ i in t, paperProb q ε₁ ε₂ i +
            (((-1 : ℝ) ^ (insert s t).card) / ((insert s t).card + 1)) *
              ∏ i in insert s t, paperProb q ε₁ ε₂ i
          =
            (((( -1 : ℝ) ^ t.card) / (t.card + 1)) +
              (((-1 : ℝ) ^ (t.card + 1)) / (t.card + 2))) *
                ∏ i in t, paperProb q ε₁ ε₂ i := by
                  rw [hcard, hprod]
                  norm_num
                  ring
        _ = (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
              ∏ i in t, paperProb q ε₁ ε₂ i := by
              rw [hcoeff]
    · intro a ha b hb hab
      have ha_not : s ∉ a := by
        intro hsa
        exact hs_not_mem ((Finset.mem_powerset.mp ha) hsa)
      have hb_not : s ∉ b := by
        intro hsb
        exact hs_not_mem ((Finset.mem_powerset.mp hb) hsb)
      have h := congrArg (Finset.erase · s) hab
      simpa [Finset.erase_insert, ha_not, hb_not] using h
  · refine Finset.disjoint_left.mpr ?_
    intro t ht_left ht_right
    rcases Finset.mem_image.mp ht_right with ⟨u, _hu, hut⟩
    have hs_mem : s ∈ t := by
      rw [← hut]
      simp
    have hs_not : s ∉ t := by
      intro hst
      exact hs_not_mem ((Finset.mem_powerset.mp ht_left) hst)
    exact hs_not hs_mem

theorem paperAlt_eq_paperAltGapZeroScaled_one
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : s ≠ r) (hs : gap q s = 0) :
    paperAlt q r ε₁ ε₂ = paperAltGapZeroScaled q r s ε₁ ε₂ 1 := by
  rw [paperAlt_eq_sum_erase_gap_zero q r s ε₁ ε₂ hrs hs]
  unfold paperAltGapZeroScaled
  apply Finset.sum_congr rfl
  intro t _ht
  simp

theorem paperGapZeroDoublePrimitive_eq_sum
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    paperGapZeroDoublePrimitive q r s ε₁ ε₂ =
      fun c =>
        ∑ t in ((Finset.univ.erase r).erase s).powerset,
          (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
            (c ^ (t.card + 2)) * ∏ i in t, paperProb q ε₁ ε₂ i := by
  funext c
  unfold paperGapZeroDoublePrimitive paperAltGapZeroScaled
  -- Push the outer factor `c^2` inside the finite sum so that each summand is a
  -- single power `c^(t.card + 2)`.
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [pow_add]
  ring

theorem paperPrimitiveScaled_eq_sum
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    paperPrimitiveScaled q r ε₁ ε₂ =
      fun c =>
        ∑ t in (Finset.univ.erase r).powerset,
          (((-1 : ℝ) ^ t.card) / (t.card + 1)) * (c ^ (t.card + 1)) *
            ∏ i in t, paperProb q ε₁ ε₂ i := by
  funext c
  unfold paperPrimitiveScaled paperAltScaled
  -- Similarly, rewrite `c * paperAltScaled ... c` as a single power inside each summand.
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [pow_succ']
  ring

theorem hasDerivAt_paperGapZeroDoublePrimitive
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) :
    HasDerivAt
      (paperGapZeroDoublePrimitive q r s ε₁ ε₂)
      (∑ t in ((Finset.univ.erase r).erase s).powerset,
        (((-1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) *
          ((t.card + 2 : ℝ) * c ^ (t.card + 1)) *
            ∏ i in t, paperProb q ε₁ ε₂ i)
      c := by
  rw [paperGapZeroDoublePrimitive_eq_sum]
  exact HasDerivAt.sum (fun t _ht => by
    have hpow : HasDerivAt (fun x : ℝ => x ^ (t.card + 2)) ((t.card + 2 : ℝ) * c ^ (t.card + 1)) c := by
      simpa using hasDerivAt_pow (t.card + 2) c
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hpow.const_mul
        (((( -1 : ℝ) ^ t.card) / ((t.card + 1) * (t.card + 2))) * ∏ i in t, paperProb q ε₁ ε₂ i))

theorem deriv_paperGapZeroDoublePrimitive_eq_paperGapZeroPrimitive
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) :
    deriv (paperGapZeroDoublePrimitive q r s ε₁ ε₂) c =
      paperGapZeroPrimitive q r s ε₁ ε₂ c := by
  rw [(hasDerivAt_paperGapZeroDoublePrimitive q r s ε₁ ε₂ c).deriv]
  unfold paperGapZeroPrimitive
  apply Finset.sum_congr rfl
  intro t _ht
  have hne : ((t.card : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hne]
  ring

theorem hasDerivAt_paperGapZeroPrimitive
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) :
    HasDerivAt
      (paperGapZeroPrimitive q r s ε₁ ε₂)
      (∏ i in ((Finset.univ.erase r).erase s), (1 - c * paperProb q ε₁ ε₂ i))
      c := by
  unfold paperGapZeroPrimitive
  have hsum :
      HasDerivAt
        (fun x =>
          ∑ t in ((Finset.univ.erase r).erase s).powerset,
            (((-1 : ℝ) ^ t.card) / (t.card + 1)) * (x ^ (t.card + 1)) *
              ∏ i in t, paperProb q ε₁ ε₂ i)
        (∑ t in ((Finset.univ.erase r).erase s).powerset,
          (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ((t.card + 1 : ℝ) * c ^ t.card) *
            ∏ i in t, paperProb q ε₁ ε₂ i)
        c := by
          exact HasDerivAt.sum (fun t _ht => by
            have hpow : HasDerivAt (fun x : ℝ => x ^ (t.card + 1)) ((t.card + 1 : ℝ) * c ^ t.card) c := by
              simpa using hasDerivAt_pow (t.card + 1) c
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              hpow.const_mul
                (((( -1 : ℝ) ^ t.card) / (t.card + 1)) * ∏ i in t, paperProb q ε₁ ε₂ i))
  have hderivEq :
      (∑ t in ((Finset.univ.erase r).erase s).powerset,
        (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ((t.card + 1 : ℝ) * c ^ t.card) *
          ∏ i in t, paperProb q ε₁ ε₂ i)
        =
      ∏ i in ((Finset.univ.erase r).erase s), (1 - c * paperProb q ε₁ ε₂ i) := by
        calc
          ∑ t in ((Finset.univ.erase r).erase s).powerset,
              (((-1 : ℝ) ^ t.card) / (t.card + 1)) * ((t.card + 1 : ℝ) * c ^ t.card) *
                ∏ i in t, paperProb q ε₁ ε₂ i
            = ∑ t in ((Finset.univ.erase r).erase s).powerset,
                (((-1 : ℝ) ^ t.card) * (c ^ t.card)) * ∏ i in t, paperProb q ε₁ ε₂ i := by
                  apply Finset.sum_congr rfl
                  intro t _ht
                  have hne : ((t.card : ℝ) + 1) ≠ 0 := by positivity
                  field_simp [hne]
                  ring
          _ = ∑ t in ((Finset.univ.erase r).erase s).powerset,
                ∏ i in t, (-(c * paperProb q ε₁ ε₂ i)) := by
                  apply Finset.sum_congr rfl
                  intro t _ht
                  have hpowneg : ((-c : ℝ) ^ t.card) = ((-1 : ℝ) ^ t.card) * c ^ t.card := by
                    rw [neg_eq_neg_one_mul, mul_pow]
                  calc
                    (((-1 : ℝ) ^ t.card) * (c ^ t.card)) * ∏ i in t, paperProb q ε₁ ε₂ i
                      = ((-c : ℝ) ^ t.card) * ∏ i in t, paperProb q ε₁ ε₂ i := by
                          rw [hpowneg]
                    _ = (∏ _i in t, (-c : ℝ)) * ∏ i in t, paperProb q ε₁ ε₂ i := by
                          rw [Finset.prod_const]
                    _ = ∏ i in t, ((-c : ℝ) * paperProb q ε₁ ε₂ i) := by
                          rw [← Finset.prod_mul_distrib]
                    _ = ∏ i in t, (-(c * paperProb q ε₁ ε₂ i)) := by
                          apply Finset.prod_congr rfl
                          intro i _hi
                          ring
          _ = ∏ i in ((Finset.univ.erase r).erase s), (1 - c * paperProb q ε₁ ε₂ i) := by
                exact sum_powerset_neg_prod_eq_prod_one_sub (((Finset.univ.erase r).erase s)) (fun i => c * paperProb q ε₁ ε₂ i)
  exact hderivEq ▸ hsum

theorem paperGapZeroPrimitive_monotoneOn_Icc
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    MonotoneOn (paperGapZeroPrimitive q r s ε₁ ε₂) (Set.Icc (0 : ℝ) 1) := by
  have hdiff : Differentiable ℝ (paperGapZeroPrimitive q r s ε₁ ε₂) := by
    intro x
    exact (hasDerivAt_paperGapZeroPrimitive q r s ε₁ ε₂ x).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rcases hx with ⟨hx0, hx1⟩
  rw [(hasDerivAt_paperGapZeroPrimitive q r s ε₁ ε₂ x).deriv]
  apply Finset.prod_nonneg
  intro i _hi
  have hpi0 : 0 ≤ paperProb q ε₁ ε₂ i := by
    unfold paperProb
    positivity
  have hpi1 : paperProb q ε₁ ε₂ i ≤ 1 := by
    unfold paperProb
    have hnonneg : 0 ≤ ((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by
      positivity
    have hle : Real.exp (-((((gap q i * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) ≤ Real.exp 0 := by
      refine Real.exp_le_exp.mpr ?_
      linarith
    simpa using hle
  have hmul : 0 ≤ x * paperProb q ε₁ ε₂ i ∧ x * paperProb q ε₁ ε₂ i ≤ 1 := by
    constructor
    · exact mul_nonneg hx0.le hpi0
    · have _hxle : x ≤ 1 := hx1.le
      nlinarith
  linarith

theorem paperGapZeroDoublePrimitive_convexOn_Icc
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (paperGapZeroDoublePrimitive q r s ε₁ ε₂) := by
  have hcont :
      ContinuousOn (paperGapZeroDoublePrimitive q r s ε₁ ε₂) (Set.Icc (0 : ℝ) 1) := by
    have hdiff : Differentiable ℝ (paperGapZeroDoublePrimitive q r s ε₁ ε₂) := by
      intro x
      exact (hasDerivAt_paperGapZeroDoublePrimitive q r s ε₁ ε₂ x).differentiableAt
    exact hdiff.continuous.continuousOn
  have hderiv :
      DifferentiableOn ℝ (paperGapZeroDoublePrimitive q r s ε₁ ε₂) (interior (Set.Icc (0 : ℝ) 1)) := by
    intro x _hx
    exact (hasDerivAt_paperGapZeroDoublePrimitive q r s ε₁ ε₂ x).differentiableAt.differentiableWithinAt
  have hmono :
      MonotoneOn (deriv (paperGapZeroDoublePrimitive q r s ε₁ ε₂)) (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [show interior (Set.Icc (0 : ℝ) 1) = Set.Ioo (0 : ℝ) 1 by rw [interior_Icc]]
    intro x hx y hy hxy
    rw [deriv_paperGapZeroDoublePrimitive_eq_paperGapZeroPrimitive,
        deriv_paperGapZeroDoublePrimitive_eq_paperGapZeroPrimitive]
    exact paperGapZeroPrimitive_monotoneOn_Icc q r s ε₁ ε₂
      (show x ∈ Set.Icc (0 : ℝ) 1 by exact ⟨hx.1.le, hx.2.le⟩)
      (show y ∈ Set.Icc (0 : ℝ) 1 by exact ⟨hy.1.le, hy.2.le⟩)
      hxy
  exact hmono.convexOn_of_deriv
    (convex_Icc (0 : ℝ) 1)
    hcont
    hderiv

theorem paperGapZeroDoublePrimitive_monotoneOn_Icc
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    MonotoneOn (paperGapZeroDoublePrimitive q r s ε₁ ε₂) (Set.Icc (0 : ℝ) 1) := by
  have hdiff : Differentiable ℝ (paperGapZeroDoublePrimitive q r s ε₁ ε₂) := by
    intro x
    exact (hasDerivAt_paperGapZeroDoublePrimitive q r s ε₁ ε₂ x).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn ?_
  intro x hx
  rw [interior_Icc] at hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  rw [deriv_paperGapZeroDoublePrimitive_eq_paperGapZeroPrimitive]
  have hmono := paperGapZeroPrimitive_monotoneOn_Icc q r s ε₁ ε₂
  have h0x := hmono (by simp) hx' hx.1.le
  have hzero : paperGapZeroPrimitive q r s ε₁ ε₂ 0 = 0 := by
    simp [paperGapZeroPrimitive]
  linarith

theorem paperAltGapZeroScaled_mul_le_paperAltGapZero
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c * paperAltGapZeroScaled q r s ε₁ ε₂ c ≤ paperAltGapZeroScaled q r s ε₁ ε₂ 1 := by
  have hconv := paperGapZeroDoublePrimitive_convexOn_Icc q r s ε₁ ε₂
  have hc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc0, hc1⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  by_cases hcz : c = 0
  · subst hcz
    have hmono := paperGapZeroDoublePrimitive_monotoneOn_Icc q r s ε₁ ε₂
    have h01 := hmono
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
      (show (0 : ℝ) ≤ 1 by norm_num)
    simpa [paperGapZeroDoublePrimitive] using h01
  · have hsec :=
      hconv.secant_mono
        (by simp)
        hc
        h1
        hcz
        (by norm_num)
        hc1
    have hzero : paperGapZeroDoublePrimitive q r s ε₁ ε₂ 0 = 0 := by
      simp [paperGapZeroDoublePrimitive]
    have hc_eq :
        (paperGapZeroDoublePrimitive q r s ε₁ ε₂ c -
            paperGapZeroDoublePrimitive q r s ε₁ ε₂ 0) / (c - 0) =
          c * paperAltGapZeroScaled q r s ε₁ ε₂ c := by
      field_simp [paperGapZeroDoublePrimitive, hcz]
      ring
    have h1_eq :
        (paperGapZeroDoublePrimitive q r s ε₁ ε₂ 1 -
            paperGapZeroDoublePrimitive q r s ε₁ ε₂ 0) / (1 - 0) =
          paperAltGapZeroScaled q r s ε₁ ε₂ 1 := by
      simp [paperGapZeroDoublePrimitive]
    rw [hc_eq, h1_eq] at hsec
    exact hsec


def paperPrimitivePoly {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) (c : ℝ) : ℝ :=
  ∑ t in (Finset.univ.erase r).powerset,
    (((-1 : ℝ) ^ t.card) / (t.card + 1)) * (c ^ (t.card + 1)) *
      ∏ i in t, paperProb q ε₁ ε₂ i

@[simp]
theorem paperPrimitiveScaled_eq_paperPrimitivePoly
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    paperPrimitiveScaled q r ε₁ ε₂ = paperPrimitivePoly q r ε₁ ε₂ := by
  funext c
  simp [paperPrimitivePoly, paperPrimitiveScaled_eq_sum]


end PermuteAndFlip
end SLang
