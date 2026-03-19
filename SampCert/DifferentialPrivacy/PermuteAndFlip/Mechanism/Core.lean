/-
Copyright (c) 2026 Michael Shoemate.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.SLang
import SampCert.Samplers.BernoulliNegativeExponential.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Lattice
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
Core mechanism definitions and selector-level lemmas.

Reading guide:
- first read the score transformations `bumpScore`, `lowerScore`, and `gap`;
- then `exactCoinPMF`, `selectPMFCore`, and `selectSLangCore`;
- finally the permutation and shift lemmas that later modules reuse.
-/

/-- We model the mechanism over a finite candidate set of size `n + 1`. -/
abbrev CandidateCount := ℕ
/-- A score vector assigns a natural-valued score to each candidate. -/
abbrev Scores (n : CandidateCount) := Fin n.succ → ℕ

/-! ### Score transforms and gap algebra -/

/-- The maximum score in a finite score vector. -/
def maxScore {n : CandidateCount} (q : Scores n) : ℕ :=
  Finset.sup Finset.univ q

/-- Raise the distinguished candidate `r` by `k`. -/
def bumpScore {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (k : ℕ) : Scores n :=
  fun i => q i + if i = r then k else 0

/-- Lower the distinguished candidate `r` by `k`, clipping at `0` in `ℕ`. -/
def lowerScore {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (k : ℕ) : Scores n :=
  fun i => q i - if i = r then k else 0

theorem lowerScore_add {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (a b : ℕ) :
    lowerScore (lowerScore q r a) r b = lowerScore q r (a + b) := by
  funext i
  by_cases hi : i = r
  · subst hi
    simp [lowerScore, Nat.sub_sub]
  · simp [lowerScore, hi]

def lowerOthersAlong {n : CandidateCount}
    (l : List (Fin n.succ)) (q q' : Scores n) (r : Fin n.succ) : Scores n :=
  match l with
  | [] => q
  | s :: l =>
      if s = r then
        lowerOthersAlong l q q' r
      else
        lowerOthersAlong l (lowerScore q s (q s - q' s)) q' r

def permuteScores {n : CandidateCount} (τ : Equiv.Perm (Fin n.succ)) (q : Scores n) : Scores n :=
  fun i => q (τ.symm i)

@[simp]
theorem probPure_apply_eq_pure_apply {α : Type} (a x : α) :
    (probPure a : SLang α) x = PMF.pure a x := rfl

/--
`gap q i` is the amount by which `i` trails the current maximum. It is the key
quantity in permute-and-flip: the acceptance probability for `i` decays
exponentially in this gap.
-/
def gap {n : CandidateCount} (q : Scores n) (i : Fin n.succ) : ℕ :=
  Finset.sup Finset.univ fun j => q j - q i

theorem exists_argmax {n : CandidateCount} (q : Scores n) :
    ∃ i : Fin n.succ, q i = maxScore q := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ q ⟨0, by simp⟩
  refine ⟨i, le_antisymm (Finset.le_sup (s := Finset.univ) (f := q) (by simp)) ?_⟩
  exact Finset.sup_le (fun j _ => hi j (by simp))

theorem gap_eq_maxScore_sub {n : CandidateCount} (q : Scores n) (i : Fin n.succ) :
    gap q i = maxScore q - q i := by
  -- The supremum over `j ↦ q j - q i` is attained at an argmax of `q`.
  refine le_antisymm ?_ ?_
  · unfold gap maxScore
    refine Finset.sup_le ?_
    intro j _
    exact Nat.sub_le_sub_right (Finset.le_sup (s := Finset.univ) (f := q) (by simp)) (q i)
  · obtain ⟨m, hm⟩ := exists_argmax q
    rw [← hm]
    unfold gap
    exact Finset.le_sup (s := Finset.univ) (f := fun j => q j - q i) (by simp)

theorem maxScore_bumpScore_of_le {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (k : ℕ) (h : q r + k ≤ maxScore q) :
    maxScore (bumpScore q r k) = maxScore q := by
  -- If raising `r` still leaves it below the old maximum, then the maximum value
  -- itself does not change.
  refine le_antisymm ?_ ?_
  · unfold maxScore bumpScore
    refine Finset.sup_le ?_
    intro i _
    by_cases hi : i = r
    · subst hi
      simpa using h
    · simpa [hi] using Finset.le_sup (s := Finset.univ) (f := q) (by simp : i ∈ Finset.univ)
  · obtain ⟨m, hm⟩ := exists_argmax q
    rw [← hm]
    unfold maxScore bumpScore
    calc
      q m ≤ q m + if m = r then k else 0 := by
        by_cases hm' : m = r <;> simp [hm']
      _ ≤ Finset.sup Finset.univ (fun i => q i + if i = r then k else 0) :=
        Finset.le_sup (s := Finset.univ) (f := fun i => q i + if i = r then k else 0) (by simp)

theorem gap_bumpScore_self_of_le {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (k : ℕ) (h : q r + k ≤ maxScore q) :
    gap (bumpScore q r k) r = gap q r - k := by
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub, maxScore_bumpScore_of_le q r k h]
  simp [bumpScore]
  omega

theorem gap_bumpScore_other_of_le {n : CandidateCount}
    (q : Scores n) (r i : Fin n.succ) (k : ℕ) (hi : i ≠ r) (h : q r + k ≤ maxScore q) :
    gap (bumpScore q r k) i = gap q i := by
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub, maxScore_bumpScore_of_le q r k h]
  simp [bumpScore, hi]

theorem maxScore_bumpScore_of_ge {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (k : ℕ) (h : maxScore q ≤ q r + k) :
    maxScore (bumpScore q r k) = q r + k := by
  -- Once `r` reaches or exceeds the old maximum, it becomes a maximizer in the
  -- bumped score vector, so the new maximum is exactly its bumped score.
  refine le_antisymm ?_ ?_
  · unfold maxScore bumpScore
    refine Finset.sup_le ?_
    intro i _
    by_cases hi : i = r
    · subst hi
      simp
    · have hqi : q i ≤ maxScore q := Finset.le_sup (s := Finset.univ) (f := q) (by simp)
      calc
        (q i + if i = r then k else 0) = q i := by simp [hi]
        _ ≤ maxScore q := hqi
        _ ≤ q r + k := h
  · unfold maxScore bumpScore
    simpa using
      (Finset.le_sup (s := Finset.univ) (f := fun i => q i + if i = r then k else 0) (by simp : r ∈ Finset.univ))

theorem gap_bumpScore_self_of_ge {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (k : ℕ) (h : maxScore q ≤ q r + k) :
    gap (bumpScore q r k) r = 0 := by
  rw [gap_eq_maxScore_sub, maxScore_bumpScore_of_ge q r k h]
  simp [bumpScore]

theorem maxScore_eq_of_gap_zero {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (hgap : gap q r = 0) :
    maxScore q = q r := by
  rw [gap_eq_maxScore_sub] at hgap
  exact le_antisymm (Nat.sub_eq_zero_iff_le.mp hgap)
    (Finset.le_sup (s := Finset.univ) (f := q) (by simp))

theorem gap_bumpScore_other_of_gap_zero {n : CandidateCount}
    (q : Scores n) (r i : Fin n.succ) (k : ℕ) (hi : i ≠ r) (hgap : gap q r = 0) :
    gap (bumpScore q r k) i = gap q i + k := by
  -- If `r` is already a maximizer, bumping `r` by `k` leaves every other score
  -- unchanged but moves the maximum up by `k`, so every competing gap grows by `k`.
  have hmax : maxScore q = q r := maxScore_eq_of_gap_zero q r hgap
  have hle : q i ≤ q r := by
    rw [← hmax]
    exact Finset.le_sup (s := Finset.univ) (f := q) (by simp)
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub, maxScore_bumpScore_of_ge q r k]
  · rw [hmax]
    simp [bumpScore, hi]
    omega
  · simp [hmax]

theorem bumpScore_add {n : CandidateCount}
    (q : Scores n) (r : Fin n.succ) (k₁ k₂ : ℕ) :
    bumpScore (bumpScore q r k₁) r k₂ = bumpScore q r (k₁ + k₂) := by
  funext i
  by_cases hi : i = r
  · subst hi
    simp [bumpScore, Nat.add_assoc]
  · simp [bumpScore, hi]

theorem gap_lowerScore_self_of_max_eq {n : CandidateCount}
    (q : Scores n) (s : Fin n.succ) (k : ℕ)
    (hk : k ≤ q s)
    (hmax : maxScore (lowerScore q s k) = maxScore q) :
    gap (lowerScore q s k) s = gap q s + k := by
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub, hmax]
  simp [lowerScore]
  have hs : q s - k + k = q s := Nat.sub_add_cancel hk
  have hq : q s ≤ maxScore q := Finset.le_sup (s := Finset.univ) (f := q) (by simp)
  omega

theorem gap_lowerScore_other_of_max_eq {n : CandidateCount}
    (q : Scores n) (s i : Fin n.succ) (k : ℕ)
    (hi : i ≠ s)
    (hmax : maxScore (lowerScore q s k) = maxScore q) :
    gap (lowerScore q s k) i = gap q i := by
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub, hmax]
  simp [lowerScore, hi]

theorem maxScore_lowerScore_unique_max_one {n : CandidateCount}
    (q : Scores n) (s : Fin n.succ)
    (huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s) :
    maxScore (lowerScore q s 1) = q s - 1 := by
  refine le_antisymm ?_ ?_
  · unfold maxScore lowerScore
    refine Finset.sup_le ?_
    intro i
    by_cases his : i = s
    · subst his
      simp [lowerScore]
    · have hlt : q i < q s := huniq i his
      have hle : q i ≤ q s - 1 := Nat.le_pred_of_lt hlt
      simpa [lowerScore, his] using hle
  · unfold maxScore lowerScore
    simpa [lowerScore] using
      (Finset.le_sup (s := Finset.univ)
        (f := fun i => q i - if i = s then 1 else 0) (by simp : s ∈ Finset.univ))

theorem maxScore_eq_of_unique_max {n : CandidateCount}
    (q : Scores n) (s : Fin n.succ)
    (huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s) :
    maxScore q = q s := by
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _hi
    by_cases his : i = s
    · simp [his]
    · exact le_of_lt (huniq i his)
  · exact Finset.le_sup (s := Finset.univ) (f := q) (by simp)

theorem gap_lowerScore_other_of_unique_max_one {n : CandidateCount}
    (q : Scores n) (s i : Fin n.succ)
    (hi : i ≠ s)
    (huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s) :
    gap (lowerScore q s 1) i = gap q i - 1 := by
  -- Lowering the unique maximizer by one decreases the maximum by one while
  -- leaving the competing score `q i` untouched.
  have hmax : maxScore (lowerScore q s 1) = q s - 1 :=
    maxScore_lowerScore_unique_max_one q s huniq
  have hold : maxScore q = q s := maxScore_eq_of_unique_max q s huniq
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub, hmax, hold]
  simp [lowerScore, hi]
  have hlt : q i < q s := huniq i hi
  omega

@[simp]
theorem gap_shift {n : CandidateCount} (q : Scores n) (c : ℕ) (i : Fin n.succ) :
    gap (fun j => q j + c) i = gap q i := by
  unfold gap
  refine Finset.sup_congr rfl ?_
  intro j _
  simp [Nat.add_sub_add_right]

@[simp]
theorem gap_permute {n : CandidateCount} (τ : Equiv.Perm (Fin n.succ)) (q : Scores n) (i : Fin n.succ) :
    gap (permuteScores τ q) (τ i) = gap q i := by
  unfold gap permuteScores
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro j _
    have h :
        (fun k => q k - q i) (τ.symm j) ≤
          Finset.univ.sup (fun k => q k - q i) :=
      Finset.le_sup (s := Finset.univ) (f := fun k => q k - q i) (Finset.mem_univ (τ.symm j))
    simpa using h
  · refine Finset.sup_le ?_
    intro j _
    have h :
        (fun k => q (τ.symm k) - q (τ.symm (τ i))) (τ j) ≤
          Finset.univ.sup (fun k => q (τ.symm k) - q (τ.symm (τ i))) :=
      Finset.le_sup
        (s := Finset.univ)
        (f := fun k => q (τ.symm k) - q (τ.symm (τ i)))
        (Finset.mem_univ (τ j))
    simpa using h

theorem exists_gap_zero {n : CandidateCount} (q : Scores n) :
    ∃ i : Fin n.succ, gap q i = 0 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ q ⟨0, by simp⟩
  refine ⟨i, le_antisymm ?_ (Nat.zero_le _)⟩
  refine Finset.sup_le ?_
  intro j _
  exact Nat.sub_eq_zero_of_le (hi j (by simp)) ▸ Nat.zero_le 0

def exactCoinPMF (num : ℕ) (den : ℕ+) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal (Real.exp (- ((num : NNReal) / den)))) (by
    have hnonneg : 0 ≤ ((num : NNReal) / den : ℝ) := by positivity
    have hle : Real.exp (-((num : NNReal) / den : ℝ)) ≤ Real.exp 0 := by
      exact Real.exp_le_exp.mpr (by linarith)
    have h' : ENNReal.ofReal (Real.exp (- ((num : NNReal) / den : ℝ))) ≤ ENNReal.ofReal 1 := by
      exact ENNReal.ofReal_le_ofReal (by simpa using hle)
    simpa using h')

@[simp]
theorem exactCoinPMF_apply_true (num : ℕ) (den : ℕ+) :
    exactCoinPMF num den true = ENNReal.ofReal (Real.exp (- ((num : NNReal) / den))) := by
  simp [exactCoinPMF]

@[simp]
theorem exactCoinPMF_zero_apply_true (den : ℕ+) :
    exactCoinPMF 0 den true = 1 := by
  rw [exactCoinPMF_apply_true]
  simp

@[simp]
theorem exactCoinPMF_apply_false (num : ℕ) (den : ℕ+) :
    exactCoinPMF num den false = 1 - ENNReal.ofReal (Real.exp (- ((num : NNReal) / den))) := by
  simp [exactCoinPMF]

@[simp]
theorem exactCoinPMF_zero_apply_false (den : ℕ+) :
    exactCoinPMF 0 den false = 0 := by
  rw [exactCoinPMF_apply_false]
  simp

theorem exactCoinPMF_true_mul_exactCoinPMF_true
    (a b : ℕ) (den : ℕ+) :
    ENNReal.ofReal (Real.exp (- ((a : NNReal) / den))) * exactCoinPMF b den true =
      exactCoinPMF (a + b) den true := by
  -- Multiplying two exact exponential factors adds their exponents.
  rw [exactCoinPMF_apply_true, exactCoinPMF_apply_true]
  rw [← ENNReal.ofReal_mul]
  · congr 1
    rw [← Real.exp_add]
    congr 1
    have hden : (((den : NNReal) : ℝ)) ≠ 0 := by positivity
    field_simp [hden]
    ring
  · positivity

theorem exactCoinPMF_false_mono
    (a b : ℕ) (den : ℕ+) (hab : a ≤ b) :
    exactCoinPMF a den false ≤ exactCoinPMF b den false := by
  -- The rejection probability `1 - exp(-x)` is monotone increasing in `x`.
  rw [exactCoinPMF_apply_false, exactCoinPMF_apply_false]
  apply tsub_le_tsub_left
  apply ENNReal.ofReal_le_ofReal
  have hab' : ((a : NNReal) : ℝ) ≤ ((b : NNReal) : ℝ) := by exact_mod_cast hab
  have hden : (0 : ℝ) ≤ ((den : NNReal) : ℝ) := by positivity
  have hdiv : (((a : NNReal) / den : NNReal) : ℝ) ≤ (((b : NNReal) / den : NNReal) : ℝ) := by
    exact div_le_div_of_nonneg_right hab' hden
  have hneg : -((((b : NNReal) / den : NNReal) : ℝ)) ≤ -((((a : NNReal) / den : NNReal) : ℝ)) := by
    linarith
  exact Real.exp_le_exp.mpr hneg

theorem bernoulliExpNegSample_eq_exactCoinPMF (num : ℕ) (den : ℕ+) :
    (BernoulliExpNegSample num den : SLang Bool) = exactCoinPMF num den := by
  ext b
  cases b <;> simp [exactCoinPMF, BernoulliExpNegSample_apply_true, BernoulliExpNegSample_apply_false]

def selectPMFCore {n : CandidateCount} :
    List (Fin n.succ) → Scores n → ℕ → ℕ+ → PMF (Option (Fin n.succ))
  | [], _, _, _ => PMF.pure none
  | i :: is, q, ε₁, ε₂ => do
      -- Sample the exact Bernoulli test for the current candidate `i`.
      let b ← exactCoinPMF (gap q i * ε₁) ε₂
      if b then
        -- Accept immediately and stop scanning.
        PMF.pure (some i)
      else
        -- Otherwise continue with the remaining candidates.
        selectPMFCore is q ε₁ ε₂

def collapseOptionPMF {α : Type} [Inhabited α] (p : PMF (Option α)) : PMF α :=
  p.bind fun o =>
    match o with
    | some a => PMF.pure a
    -- This fallback is only used for the raw recursive selector. Later lemmas
    -- show it has zero mass on the full candidate list.
    | none => PMF.pure default

def selectPMF {n : CandidateCount} : List (Fin n.succ) → Scores n → ℕ → ℕ+ → PMF (Fin n.succ)
  | l, q, ε₁, ε₂ => collapseOptionPMF (selectPMFCore l q ε₁ ε₂)

def selectSLangCore {n : CandidateCount} :
    List (Fin n.succ) → Scores n → ℕ → ℕ+ → SLang (Option (Fin n.succ))
  | [], _, _, _ => return none
  | i :: is, q, ε₁, ε₂ => do
      let b ← BernoulliExpNegSample (gap q i * ε₁) ε₂
      if b then
        return some i
      else
        selectSLangCore is q ε₁ ε₂

def collapseOptionSLang {α : Type} [Inhabited α] (p : SLang (Option α)) : SLang α := do
  let o ← p
  match o with
  | some a => return a
  | none => return default

def selectSLang {n : CandidateCount} : List (Fin n.succ) → Scores n → ℕ → ℕ+ → SLang (Fin n.succ)
  | l, q, ε₁, ε₂ => collapseOptionSLang (selectSLangCore l q ε₁ ε₂)

@[simp]
theorem selectSLangCore_eq_selectPMFCore {n : CandidateCount}
    (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    selectSLangCore l q ε₁ ε₂ = selectPMFCore l q ε₁ ε₂ := by
  induction l with
  | nil =>
      ext i
      simp [selectSLangCore, selectPMFCore]
  | cons a l ih =>
      ext i
      unfold selectSLangCore selectPMFCore
      rw [bernoulliExpNegSample_eq_exactCoinPMF]
      apply tsum_congr
      intro b
      by_cases hb : b = true
      · subst hb
        simp [probPure_apply_eq_pure_apply]
      · simp [hb, ih]

@[simp]
theorem selectSLang_eq_selectPMF {n : CandidateCount}
    (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    selectSLang l q ε₁ ε₂ = selectPMF l q ε₁ ε₂ := by
  ext i
  simp [selectSLang, selectPMF, collapseOptionSLang, collapseOptionPMF, selectSLangCore_eq_selectPMFCore]
  apply tsum_congr
  intro a
  cases a <;> rfl

@[simp]
theorem selectPMFCore_permute {n : CandidateCount}
    (τ : Equiv.Perm (Fin n.succ)) (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (o : Option (Fin n.succ)) :
    selectPMFCore (l.map τ) (permuteScores τ q) ε₁ ε₂ (o.map τ) = selectPMFCore l q ε₁ ε₂ o := by
  induction l with
  | nil =>
      cases o <;> simp [selectPMFCore]
  | cons a l ih =>
      cases o with
      | none =>
          unfold selectPMFCore
          simp [gap_permute]
          apply tsum_congr
          intro b
          by_cases hb : b = true
          · subst hb
            simp [probPure_apply_eq_pure_apply]
          · simp [hb]
            exact congrArg
              (fun t => (1 - ENNReal.ofReal (Real.exp (-((gap q a * ε₁ : NNReal) / ε₂)))) * t) ih
      | some r =>
          unfold selectPMFCore
          simp [gap_permute]
          apply tsum_congr
          intro b
          by_cases hb : b = true
          · subst hb
            simp [probPure_apply_eq_pure_apply]
          · simp [hb]
            exact congrArg
              (fun t => (1 - ENNReal.ofReal (Real.exp (-((gap q a * ε₁ : NNReal) / ε₂)))) * t) ih

@[simp]
theorem selectPMFCore_shift {n : CandidateCount}
    (l : List (Fin n.succ)) (q : Scores n) (c ε₁ : ℕ) (ε₂ : ℕ+) :
    selectPMFCore l (fun j => q j + c) ε₁ ε₂ = selectPMFCore l q ε₁ ε₂ := by
  induction l with
  | nil =>
      simp [selectPMFCore]
  | cons a l ih =>
      simp [selectPMFCore, gap_shift, ih]

theorem selectPMFCore_none_of_gap_zero {n : CandidateCount}
    (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    {i : Fin n.succ} (hi : i ∈ l) (hgap : gap q i = 0) :
    selectPMFCore l q ε₁ ε₂ none = 0 := by
  revert i
  induction l with
  | nil =>
      intro i hi
      cases hi
  | cons a l ih =>
      intro i hi hgap
      simp at hi
      rcases hi with rfl | hi
      · unfold selectPMFCore
        simp [hgap, exactCoinPMF_zero_apply_true, exactCoinPMF_zero_apply_false]
      · unfold selectPMFCore
        have ih' := ih hi hgap
        by_cases hb : gap q a * ε₁ = 0
        · simp [hb]
        · simp [hb, ih']

theorem selectPMFCore_some_eq_zero_of_not_mem {n : CandidateCount}
    (l : List (Fin n.succ)) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    {r : Fin n.succ} (hr : r ∉ l) :
    selectPMFCore l q ε₁ ε₂ (some r) = 0 := by
  induction l with
  | nil =>
      simp [selectPMFCore]
  | cons a l ih =>
      have hra : r ≠ a := by
        intro h
        apply hr
        simp [h]
      have hrtail : r ∉ l := by
        intro h
        apply hr
        simp [h]
      unfold selectPMFCore
      by_cases hb : exactCoinPMF (gap q a * ε₁) ε₂ true = 0
      · simp [PMF.bind_apply, hb, hra, ih hrtail]
      · simp [PMF.bind_apply, hb, hra, ih hrtail]


end PermuteAndFlip
end SLang
