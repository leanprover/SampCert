/-
Copyright (c) 2026 Michael Shoemate.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic

noncomputable section

open scoped Classical

namespace SLang
namespace PermuteAndFlip

abbrev IntScores (n : ℕ) := Fin n.succ → ℤ
abbrev IntMechanism (n : ℕ) := IntScores n → PMF (Fin n.succ)

def permuteScores {n : ℕ} (τ : Equiv.Perm (Fin n.succ)) (q : IntScores n) : IntScores n :=
  fun i => q (τ.symm i)

def shiftScores {n : ℕ} (q : IntScores n) (c : ℤ) : IntScores n :=
  fun i => q i + c

def raiseScore {n : ℕ} (q : IntScores n) (r : Fin n.succ) (k : ℤ) : IntScores n :=
  fun i => q i + if i = r then k else 0

def lowerScore {n : ℕ} (q : IntScores n) (r : Fin n.succ) (k : ℤ) : IntScores n :=
  raiseScore q r (-k)

def Symmetric {n : ℕ} (M : IntMechanism n) : Prop :=
  ∀ (τ : Equiv.Perm (Fin n.succ)) (q : IntScores n) (r : Fin n.succ),
    M (permuteScores τ q) (τ r) = M q r

def ShiftInvariant {n : ℕ} (M : IntMechanism n) : Prop :=
  ∀ (q : IntScores n) (c : ℤ) (r : Fin n.succ),
    M (shiftScores q c) r = M q r

def Monotone {n : ℕ} (M : IntMechanism n) : Prop :=
  ∀ (q q' : IntScores n) (r : Fin n.succ),
    q r ≤ q' r →
    (∀ s : Fin n.succ, s ≠ r → q' s ≤ q s) →
    M q r ≤ M q' r

def Regular {n : ℕ} (M : IntMechanism n) : Prop :=
  Symmetric M ∧ ShiftInvariant M ∧ Monotone M

def boundedPerturbation {n : ℕ} (δ : ℤ) (z : Fin n.succ → ℤ) : Prop :=
  ∀ i, -δ ≤ z i ∧ z i ≤ δ

def boundedInterval {n : ℕ} (a b : ℤ) (z : Fin n.succ → ℤ) : Prop :=
  ∀ i, a ≤ z i ∧ z i ≤ b

def scoreDiff {n : ℕ} (q q' : IntScores n) : Fin n.succ → ℤ :=
  fun i => q' i - q i

def diffSet {n : ℕ} (q q' : IntScores n) : Finset ℤ :=
  Finset.univ.image (scoreDiff q q')

theorem diffSet_nonempty {n : ℕ} (q q' : IntScores n) : (diffSet q q').Nonempty := by
  have huniv : (Finset.univ : Finset (Fin n.succ)).Nonempty := ⟨0, by simp⟩
  rcases huniv with ⟨i, _hi⟩
  exact ⟨scoreDiff q q' i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩

def rangeDistance {n : ℕ} (q q' : IntScores n) : ℤ :=
  let s := diffSet q q'
  s.max' (diffSet_nonempty q q') - s.min' (diffSet_nonempty q q')

/--
Abstract regularity-to-privacy reduction.

This corresponds to the paper's Proposition 2: symmetry, shift-invariance, and
monotonicity reduce privacy to a single worst-case raise inequality on the
selected coordinate.
-/
theorem reduced_privacy_of_regular
    {n : ℕ} {M : IntMechanism n} {α : ENNReal} {δ : ℤ}
    (Hreg : Regular M)
    (Hred : ∀ (q : IntScores n) (r : Fin n.succ),
      α * M (raiseScore q r (2 * δ)) r ≤ M q r) :
    ∀ (q : IntScores n) (z : Fin n.succ → ℤ) (r : Fin n.succ),
      boundedPerturbation δ z →
      α * M q r ≤ M (fun i => q i + z i) r := by
  intro q z r hz
  rcases Hreg with ⟨_, Hshift, Hmono⟩
  have Hstep := Hred (lowerScore q r (2 * δ)) r
  have hshiftScores :
      shiftScores (lowerScore q r (2 * δ)) δ =
        (fun i => q i + if i = r then (-δ) else δ) := by
    funext i
    by_cases hi : i = r
    · subst hi
      simp [lowerScore, raiseScore, shiftScores]
      linarith
    · simp [lowerScore, raiseScore, shiftScores, hi]
  have Hshifted :
      M (lowerScore q r (2 * δ)) r =
        M (fun i => q i + if i = r then (-δ) else δ) r := by
    rw [← Hshift (lowerScore q r (2 * δ)) δ r]
    simp [hshiftScores]
  have Hr : q r - δ ≤ q r + z r := by
    have hz_r := hz r
    simp at hz_r
    linarith
  have Hs :
      ∀ s : Fin n.succ, s ≠ r →
        q s + z s ≤ q s + if s = r then (-δ) else δ := by
    intro s hs
    have hz_s := hz s
    simp [hs] at hz_s ⊢
    linarith
  have Hr' :
      (fun i => q i + if i = r then (-δ) else δ) r ≤
      (fun i => q i + z i) r := by
    have hz_r := hz r
    simp at hz_r ⊢
    linarith
  have Hmono' :=
    Hmono
      (fun i => q i + if i = r then (-δ) else δ)
      (fun i => q i + z i)
      r
      Hr'
      (by
        intro s hs
        have := Hs s hs
        simpa [hs] using this)
  have hraise :
      raiseScore (lowerScore q r (2 * δ)) r (2 * δ) = q := by
    funext i
    by_cases hi : i = r
    · subst hi
      simp [lowerScore, raiseScore]
    · simp [lowerScore, raiseScore, hi]
  calc
    α * M q r
      = α * M (raiseScore (lowerScore q r (2 * δ)) r (2 * δ)) r := by
          simp [hraise]
    _ ≤ M (lowerScore q r (2 * δ)) r := Hstep
    _ = M (fun i => q i + if i = r then (-δ) else δ) r := Hshifted
    _ ≤ M (fun i => q i + z i) r := Hmono'

/--
Abstract interval version of the regularity reduction.

This is the same reduction pattern as the paper's Proposition 2, but expressed
for an arbitrary interval `[a,b]` rather than the symmetric `[-δ, δ]` case.
-/
theorem interval_privacy_of_regular
    {n : ℕ} {M : IntMechanism n} {α : ENNReal} {a b : ℤ}
    (Hreg : Regular M)
    (Hred : ∀ (q : IntScores n) (r : Fin n.succ),
      α * M (raiseScore q r (b - a)) r ≤ M q r) :
    ∀ (q : IntScores n) (z : Fin n.succ → ℤ) (r : Fin n.succ),
      boundedInterval a b z →
      α * M q r ≤ M (fun i => q i + z i) r := by
  intro q z r hz
  rcases Hreg with ⟨_, Hshift, Hmono⟩
  have Hstep := Hred (lowerScore q r (b - a)) r
  have hshiftScores :
      shiftScores (lowerScore q r (b - a)) b =
        (fun i => q i + if i = r then a else b) := by
    funext i
    by_cases hi : i = r
    · subst hi
      simp [lowerScore, raiseScore, shiftScores]
      ring_nf
    · simp [lowerScore, raiseScore, shiftScores, hi]
  have Hshifted :
      M (lowerScore q r (b - a)) r =
        M (fun i => q i + if i = r then a else b) r := by
    rw [← Hshift (lowerScore q r (b - a)) b r]
    simp [hshiftScores]
  have Hr' :
      (fun i => q i + if i = r then a else b) r ≤
      (fun i => q i + z i) r := by
    have hz_r := hz r
    simp at hz_r ⊢
    linarith
  have Hs :
      ∀ s : Fin n.succ, s ≠ r →
        q s + z s ≤ q s + if s = r then a else b := by
    intro s hs
    have hz_s := hz s
    simp [hs] at hz_s ⊢
    linarith
  have Hmono' :=
    Hmono
      (fun i => q i + if i = r then a else b)
      (fun i => q i + z i)
      r
      Hr'
      (by
        intro s hs
        have := Hs s hs
        simpa [hs] using this)
  have hraise :
      raiseScore (lowerScore q r (b - a)) r (b - a) = q := by
    funext i
    by_cases hi : i = r
    · subst hi
      simp [lowerScore, raiseScore]
      ring
    · simp [lowerScore, raiseScore, hi]
  calc
    α * M q r
      = α * M (raiseScore (lowerScore q r (b - a)) r (b - a)) r := by
          simp [hraise]
    _ ≤ M (lowerScore q r (b - a)) r := Hstep
    _ = M (fun i => q i + if i = r then a else b) r := Hshifted
    _ ≤ M (fun i => q i + z i) r := Hmono'

theorem boundedInterval_scoreDiff
    {n : ℕ} (q q' : IntScores n) :
    boundedInterval
      ((diffSet q q').min' (diffSet_nonempty q q'))
      ((diffSet q q').max' (diffSet_nonempty q q'))
      (scoreDiff q q') := by
  intro i
  constructor
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)

theorem add_scoreDiff
    {n : ℕ} (q q' : IntScores n) :
    (fun i => q i + scoreDiff q q' i) = q' := by
  funext i
  simp [scoreDiff]

/--
Abstract privacy theorem stated directly in terms of range distance.

This theorem is not stated in the paper in exactly this form; it is the
range-distance generalization of the same regularity reduction.
-/
theorem range_privacy_of_regular
    {n : ℕ} {M : IntMechanism n} {β : ℤ → ENNReal}
    (Hreg : Regular M)
    (Hred : ∀ (k : ℤ), 0 ≤ k →
      ∀ (q : IntScores n) (r : Fin n.succ),
        β k * M (raiseScore q r k) r ≤ M q r) :
    ∀ (q q' : IntScores n) (r : Fin n.succ),
      β (rangeDistance q q') * M q r ≤ M q' r := by
  intro q q' r
  let s : Finset ℤ := diffSet q q'
  have hs : s.Nonempty := by simpa [s] using diffSet_nonempty q q'
  let a : ℤ := s.min' hs
  let b : ℤ := s.max' hs
  have hab : 0 ≤ b - a := by
    exact sub_nonneg.mpr (Finset.min'_le _ _ (Finset.max'_mem s hs))
  have hinterval :=
    interval_privacy_of_regular
      (Hreg := Hreg)
      (α := β (b - a))
      (a := a)
      (b := b)
      (Hred := Hred (b - a) hab)
      (q := q)
      (z := scoreDiff q q')
      (r := r)
      (boundedInterval_scoreDiff q q')
  have hrange : rangeDistance q q' = b - a := by
    simp [rangeDistance, s, a, b, hs]
  simpa [hrange, add_scoreDiff q q'] using hinterval

end PermuteAndFlip
end SLang
