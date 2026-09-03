/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Paper.Counting

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
Selector-weight and canonical-order lemmas for the executable selector.

Reading guide:
- `selectWeight` is the fixed-order probability of first accepting `r`;
- the `selectPMF...` lemmas connect that closed form back to the executable selector;
- the final lemmas lift fixed-order facts to canonical candidate orders.
-/

/-! ### Fixed-order selector weights -/

/--
`selectWeight l q ... r` is the probability that a fixed scan order `l`
returns `r`: every earlier candidate must fail its Bernoulli test, and `r`
must succeed when first encountered.
-/
def selectWeight {n : CandidateCount} :
    List (Fin n.succ) → Scores n → ℕ → ℕ+ → Fin n.succ → ENNReal
  | [], _, _, _, _ => 0
  | i :: is, q, ε₁, ε₂, r =>
      if i = r then
        exactCoinPMF (gap q i * ε₁) ε₂ true
      else
        exactCoinPMF (gap q i * ε₁) ε₂ false * selectWeight is q ε₁ ε₂ r

theorem selectWeight_eq_prefix_prod
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) (hr : r ∈ l) :
    selectWeight l q ε₁ ε₂ r =
      ((l.take (l.idxOf r)).map (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false)).prod *
        exactCoinPMF (gap q r * ε₁) ε₂ true := by
  induction l with
  | nil =>
      cases hr
  | cons a l ih =>
      simp at hl
      rcases hl with ⟨ha, hnodup⟩
      simp at hr
      rcases hr with rfl | hr
      · simp [selectWeight, List.idxOf_cons_self]
      · have har : a ≠ r := by
          intro h
          apply ha
          simpa [h] using hr
        rw [show selectWeight (a :: l) q ε₁ ε₂ r =
            exactCoinPMF (gap q a * ε₁) ε₂ false * selectWeight l q ε₁ ε₂ r by
              simp [selectWeight, har]]
        rw [ih hnodup hr]
        simp [har]
        ac_rfl

theorem selectWeight_map_finRange_eq_coin_mul_beforeSet_prod
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ))
    (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    selectWeight ((List.finRange n.succ).map σ) q ε₁ ε₂ r =
      exactCoinPMF (gap q r * ε₁) ε₂ true *
        Finset.prod (beforeSet σ r) (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false) := by
  have hnodup : (((List.finRange n.succ).map σ).Nodup) := by
    simpa using (List.nodup_finRange n.succ).map σ.injective
  have hr : r ∈ ((List.finRange n.succ).map σ) := by
    exact List.mem_map.mpr ⟨σ.symm r, by simp, by simp⟩
  rw [selectWeight_eq_prefix_prod ((List.finRange n.succ).map σ) hnodup q ε₁ ε₂ r hr]
  have hprod :
      (List.map (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false)
          (List.take (((List.finRange n.succ).map σ).idxOf r) ((List.finRange n.succ).map σ))).prod
        = Finset.prod (beforeSet σ r) (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false) := by
    simpa only [List.ofFn_eq_map, indexOf_map_canonicalOrder] using
      (prefix_prod_eq_beforeSet_prod σ r (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false))
  rw [hprod]
  ac_rfl

/-! ### Connecting the recursive selector to the closed form -/

theorem selectPMFCore_cons_eq_head_of_not_mem {n : CandidateCount}
    (a : Fin n.succ) (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (ha : a ∉ l) :
    selectPMFCore (a :: l) q ε₁ ε₂ (some a) = exactCoinPMF (gap q a * ε₁) ε₂ true := by
  simp [selectPMFCore, PMF.bind_apply, selectPMFCore_some_eq_zero_of_not_mem l q ε₁ ε₂ ha]

theorem selectPMFCore_cons_eq_tail_of_ne {n : CandidateCount}
    (a r : Fin n.succ) (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (har : r ≠ a) :
    selectPMFCore (a :: l) q ε₁ ε₂ (some r) =
      exactCoinPMF (gap q a * ε₁) ε₂ false * selectPMFCore l q ε₁ ε₂ (some r) := by
  simp [selectPMFCore, PMF.bind_apply, har]

@[simp]
theorem selectPMFCore_eq_selectWeight
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (r : Fin n.succ) :
    selectPMFCore l q ε₁ ε₂ (some r) = selectWeight l q ε₁ ε₂ r := by
  induction l with
  | nil =>
      simp [selectPMFCore, selectWeight]
  | cons a l ih =>
      simp at hl
      rcases hl with ⟨ha, hnodup⟩
      by_cases har : r = a
      · subst r
        rw [selectPMFCore_cons_eq_head_of_not_mem a l q ε₁ ε₂ ha]
        simp [selectWeight]
      · rw [selectPMFCore_cons_eq_tail_of_ne a r l q ε₁ ε₂ har]
        have hne : a ≠ r := by
          intro h
          exact har h.symm
        simp [selectWeight, hne, ih hnodup]

theorem selectWeight_bumpScore_self_of_gap_zero_le
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hr : r ∈ l) (hgap : gap q r = 0) :
    selectWeight l q ε₁ ε₂ r ≤
      selectWeight l (bumpScore q r k) ε₁ ε₂ r := by
  induction l generalizing q with
  | nil =>
      cases hr
  | cons a l ih =>
      simp at hl
      rcases hl with ⟨ha, hnodup⟩
      simp at hr
      rcases hr with h_eq | hr
      · subst h_eq
        -- If `r` is the head of the list, the selector weight is just the
        -- acceptance probability for `r`, which only goes up after a bump.
        have hmax : maxScore q ≤ q r + k := by
          rw [maxScore_eq_of_gap_zero q r hgap]
          exact Nat.le_add_right (q r) k
        rw [show selectWeight (r :: l) q ε₁ ε₂ r = exactCoinPMF (gap q r * ε₁) ε₂ true by
              simp [selectWeight]]
        rw [show selectWeight (r :: l) (bumpScore q r k) ε₁ ε₂ r =
              exactCoinPMF (gap (bumpScore q r k) r * ε₁) ε₂ true by
              simp [selectWeight]]
        rw [hgap, gap_bumpScore_self_of_ge q r k hmax]
      · have har : r ≠ a := by
          intro h
          apply ha
          simpa [h] using hr
        have hne : a ≠ r := har.symm
        -- Otherwise compare the head rejection probabilities and recurse on the tail.
        rw [show selectWeight (a :: l) q ε₁ ε₂ r =
              exactCoinPMF (gap q a * ε₁) ε₂ false * selectWeight l q ε₁ ε₂ r by
              simp [selectWeight, hne]]
        rw [show selectWeight (a :: l) (bumpScore q r k) ε₁ ε₂ r =
              exactCoinPMF (gap (bumpScore q r k) a * ε₁) ε₂ false *
                selectWeight l (bumpScore q r k) ε₁ ε₂ r by
              simp [selectWeight, hne]]
        have hcoin :
            exactCoinPMF (gap q a * ε₁) ε₂ false ≤
              exactCoinPMF (gap (bumpScore q r k) a * ε₁) ε₂ false := by
          apply exactCoinPMF_false_mono
          rw [gap_bumpScore_other_of_gap_zero q r a k har.symm hgap]
          exact Nat.mul_le_mul_right ε₁ (Nat.le_add_right (gap q a) k)
        exact mul_le_mul' hcoin (ih hnodup q hr hgap)

theorem selectWeight_lowerScore_other_of_max_eq_le
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q : Scores n) (r s : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) (hr : r ∈ l) (hk : k ≤ q s)
    (hmax : maxScore (lowerScore q s k) = maxScore q) :
    selectWeight l q ε₁ ε₂ r ≤
      selectWeight l (lowerScore q s k) ε₁ ε₂ r := by
  induction l generalizing q with
  | nil =>
      cases hr
  | cons a l ih =>
      simp at hl
      rcases hl with ⟨ha, hnodup⟩
      simp at hr
      rcases hr with h_eq | hr
      · subst h_eq
        -- If `r` is at the head, lowering some other candidate can only improve
        -- `r`'s head acceptance probability, provided the maximum stays fixed.
        rw [show selectWeight (r :: l) q ε₁ ε₂ r = exactCoinPMF (gap q r * ε₁) ε₂ true by
              simp [selectWeight]]
        rw [show selectWeight (r :: l) (lowerScore q s k) ε₁ ε₂ r =
              exactCoinPMF (gap (lowerScore q s k) r * ε₁) ε₂ true by
              simp [selectWeight]]
        rw [gap_lowerScore_other_of_max_eq q s r k hrs hmax]
      · have har : r ≠ a := by
          intro h
          apply ha
          simpa [h] using hr
        have hne : a ≠ r := har.symm
        -- If `r` is later in the list, compare the head rejection factor and then recurse.
        rw [show selectWeight (a :: l) q ε₁ ε₂ r =
              exactCoinPMF (gap q a * ε₁) ε₂ false * selectWeight l q ε₁ ε₂ r by
              simp [selectWeight, hne]]
        rw [show selectWeight (a :: l) (lowerScore q s k) ε₁ ε₂ r =
              exactCoinPMF (gap (lowerScore q s k) a * ε₁) ε₂ false *
                selectWeight l (lowerScore q s k) ε₁ ε₂ r by
              simp [selectWeight, hne]]
        have hcoin :
            exactCoinPMF (gap q a * ε₁) ε₂ false ≤
              exactCoinPMF (gap (lowerScore q s k) a * ε₁) ε₂ false := by
          by_cases has : a = s
          · subst has
            apply exactCoinPMF_false_mono
            rw [gap_lowerScore_self_of_max_eq q a k (by simpa using hk) hmax]
            exact Nat.mul_le_mul_right ε₁ (Nat.le_add_right (gap q a) k)
          · apply le_of_eq
            rw [gap_lowerScore_other_of_max_eq q s a k has hmax]
        have htail :
            selectWeight l q ε₁ ε₂ r ≤
              selectWeight l (lowerScore q s k) ε₁ ε₂ r := by
          simpa using (ih hnodup (q := q) hr hk hmax)
        exact mul_le_mul' hcoin htail

theorem selectPMFCore_bumpScore_self_of_le
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hr : r ∈ l) (hmax : q r + k ≤ maxScore q) :
    ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
        selectPMFCore l (bumpScore q r k) ε₁ ε₂ (some r) =
      selectPMFCore l q ε₁ ε₂ (some r) := by
  induction l generalizing q with
  | nil =>
      cases hr
  | cons a l ih =>
      simp at hl
      rcases hl with ⟨ha, hnodup⟩
      simp at hr
      rcases hr with h_eq | hr
      · subst h_eq
        -- If `r` appears first, the desired equality is exactly the multiplicative
        -- exponential identity for the head Bernoulli coin.
        rw [selectPMFCore_cons_eq_head_of_not_mem r l (bumpScore q r k) ε₁ ε₂ ha]
        rw [selectPMFCore_cons_eq_head_of_not_mem r l q ε₁ ε₂ ha]
        have hk : k ≤ gap q r := by
          rw [gap_eq_maxScore_sub]
          omega
        have hgap : gap (bumpScore q r k) r * ε₁ + k * ε₁ = gap q r * ε₁ := by
          rw [gap_bumpScore_self_of_le q r k hmax]
          calc
            (gap q r - k) * ε₁ + k * ε₁ = ((gap q r - k) + k) * ε₁ := by
              rw [Nat.add_mul]
            _ = gap q r * ε₁ := by rw [Nat.sub_add_cancel hk]
        rw [← hgap]
        simpa [Nat.add_comm] using
          exactCoinPMF_true_mul_exactCoinPMF_true (k * ε₁) (gap (bumpScore q r k) r * ε₁) ε₂
      · have har : r ≠ a := by
          intro h
          apply ha
          simpa [h] using hr
        -- If the head is some other candidate, its rejection probability is unchanged,
        -- so the statement reduces to the induction hypothesis on the tail.
        rw [selectPMFCore_cons_eq_tail_of_ne a r l (bumpScore q r k) ε₁ ε₂ har]
        rw [selectPMFCore_cons_eq_tail_of_ne a r l q ε₁ ε₂ har]
        rw [gap_bumpScore_other_of_le q r a k har.symm hmax]
        calc
          ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
              (exactCoinPMF (gap q a * ε₁) ε₂ false * selectPMFCore l (bumpScore q r k) ε₁ ε₂ (some r))
            = exactCoinPMF (gap q a * ε₁) ε₂ false *
                (ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
                  selectPMFCore l (bumpScore q r k) ε₁ ε₂ (some r)) := by
                    ac_rfl
          _ = exactCoinPMF (gap q a * ε₁) ε₂ false * selectPMFCore l q ε₁ ε₂ (some r) := by
                exact congrArg (fun x => exactCoinPMF (gap q a * ε₁) ε₂ false * x) (ih hnodup q hr hmax)

def canonicalOrder (n : CandidateCount) : List (Fin n.succ) :=
  List.finRange n.succ

theorem collapseOptionPMF_apply_of_none_zero {α : Type} [Inhabited α]
    (p : PMF (Option α)) (hp : p none = 0) (a : α) :
    collapseOptionPMF p a = p (some a) := by
  unfold collapseOptionPMF
  rw [PMF.bind_apply]
  refine (tsum_eq_single (some a) ?_).trans ?_
  · intro x hx
    cases x with
    | none =>
        simp [hp]
    | some b =>
        have hb : b ≠ a := by
          intro h
          apply hx
          simp [h]
        by_cases hab : a = b
        · exfalso
          exact hb hab.symm
        · simp [PMF.pure_apply, hab]
  · simp

theorem selectPMF_eq_selectPMFCore_map_canonicalOrder {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r =
      selectPMFCore ((canonicalOrder n).map σ) q ε₁ ε₂ (some r) := by
  obtain ⟨i, hi⟩ := exists_gap_zero q
  have hnone :
      selectPMFCore ((canonicalOrder n).map σ) q ε₁ ε₂ none = 0 := by
    -- On the full candidate list there is always some gap-zero candidate, so the
    -- recursive selector never falls off the end without accepting someone.
    exact selectPMFCore_none_of_gap_zero ((canonicalOrder n).map σ) q ε₁ ε₂ (by
      exact List.mem_map.mpr ⟨σ.symm i, by simp [canonicalOrder], by simp⟩) hi
  simp [selectPMF, collapseOptionPMF_apply_of_none_zero, hnone]

/-! ### Canonical-order lifting lemmas -/

theorem selectPMF_map_canonicalOrder_eq_selectWeight {n : CandidateCount}
    (σ : Equiv.Perm (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r =
      selectWeight ((canonicalOrder n).map σ) q ε₁ ε₂ r := by
  rw [selectPMF_eq_selectPMFCore_map_canonicalOrder σ q ε₁ ε₂ r]
  exact selectPMFCore_eq_selectWeight
    ((canonicalOrder n).map σ)
    (by simpa [canonicalOrder] using (List.nodup_finRange n.succ).map σ.injective)
    q ε₁ ε₂ r

theorem selectPMF_map_canonicalOrder_permute {n : CandidateCount}
    (σ τ : Equiv.Perm (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    selectPMF ((canonicalOrder n).map (σ.trans τ)) (permuteScores τ q) ε₁ ε₂ (τ r) =
      selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r := by
  rw [selectPMF_eq_selectPMFCore_map_canonicalOrder (σ.trans τ) (permuteScores τ q) ε₁ ε₂ (τ r)]
  rw [selectPMF_eq_selectPMFCore_map_canonicalOrder σ q ε₁ ε₂ r]
  simpa [List.map_map] using
    selectPMFCore_permute τ ((canonicalOrder n).map σ) q ε₁ ε₂ (some r)

theorem selectPMF_bumpScore_self_of_le_map_canonicalOrder
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ))
    (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hmax : q r + k ≤ maxScore q) :
    ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
        selectPMF ((canonicalOrder n).map σ) (bumpScore q r k) ε₁ ε₂ r =
      selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r := by
  rw [selectPMF_eq_selectPMFCore_map_canonicalOrder σ (bumpScore q r k) ε₁ ε₂ r]
  rw [selectPMF_eq_selectPMFCore_map_canonicalOrder σ q ε₁ ε₂ r]
  exact selectPMFCore_bumpScore_self_of_le
    (((canonicalOrder n).map σ))
    (by
      simpa [canonicalOrder] using (List.nodup_finRange n.succ).map σ.injective)
    q r k ε₁ ε₂
    (by
      exact List.mem_map.mpr ⟨σ.symm r, by simp [canonicalOrder], by simp⟩)
    hmax

theorem selectPMF_bumpScore_self_of_gap_zero_le_map_canonicalOrder
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ))
    (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hgap : gap q r = 0) :
    selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r ≤
      selectPMF ((canonicalOrder n).map σ) (bumpScore q r k) ε₁ ε₂ r := by
  rw [selectPMF_map_canonicalOrder_eq_selectWeight σ q ε₁ ε₂ r]
  rw [selectPMF_map_canonicalOrder_eq_selectWeight σ (bumpScore q r k) ε₁ ε₂ r]
  exact selectWeight_bumpScore_self_of_gap_zero_le
    (((canonicalOrder n).map σ))
    (by simpa [canonicalOrder] using (List.nodup_finRange n.succ).map σ.injective)
    q r k ε₁ ε₂
    (by exact List.mem_map.mpr ⟨σ.symm r, by simp [canonicalOrder], by simp⟩)
    hgap

theorem selectPMF_lowerScore_other_of_max_eq_le_map_canonicalOrder
    {n : CandidateCount} (σ : Equiv.Perm (Fin n.succ))
    (q : Scores n) (r s : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) (hk : k ≤ q s)
    (hmax : maxScore (lowerScore q s k) = maxScore q) :
    selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r ≤
      selectPMF ((canonicalOrder n).map σ) (lowerScore q s k) ε₁ ε₂ r := by
  rw [selectPMF_map_canonicalOrder_eq_selectWeight σ q ε₁ ε₂ r]
  rw [selectPMF_map_canonicalOrder_eq_selectWeight σ (lowerScore q s k) ε₁ ε₂ r]
  exact selectWeight_lowerScore_other_of_max_eq_le
    (((canonicalOrder n).map σ))
    (by simpa [canonicalOrder] using (List.nodup_finRange n.succ).map σ.injective)
    q r s k ε₁ ε₂
    hrs
    (by exact List.mem_map.mpr ⟨σ.symm r, by simp [canonicalOrder], by simp⟩)
    hk
    hmax
end PermuteAndFlip
end SLang
