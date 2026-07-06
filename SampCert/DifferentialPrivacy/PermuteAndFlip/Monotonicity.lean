/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.MonotonicityLocal

/-!
Monotonicity and privacy-step lemmas for permute-and-flip.

Reading order:
- `MonotonicityLocal` proves one-coordinate bump/lower lemmas.
- This file packages those into global shift invariance and monotonicity.
- It then derives the one-step and `k`-step privacy contractions used by
  [Privacy](SampCert/DifferentialPrivacy/PermuteAndFlip/Privacy.lean).
-/

noncomputable section

namespace SLang
namespace PermuteAndFlip

section Global

/--
Adding the same constant to every score does not change permute-and-flip.
This shift-invariance is used in the privacy proof to normalize
integer score differences back into natural-valued score vectors.
-/
theorem permuteAndFlipPMF_shift
    {n : CandidateCount} (q : Scores n) (c ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    permuteAndFlipPMF n (fun i => q i + c) ε₁ ε₂ r =
      permuteAndFlipPMF n q ε₁ ε₂ r := by
  unfold permuteAndFlipPMF
  -- The outer permutation average is unchanged; only the inner selector sees
  -- the shifted scores, and `selectPMFCore_shift` already proved that the
  -- selector depends only on score differences.
  apply tsum_congr
  intro σ
  simp [selectPMF, selectPMFCore_shift]

/--
Global monotonicity: increasing the selected candidate and/or decreasing every
other candidate can only increase the probability of outputting `r`.

The proof first bumps `r` up to its target score and then lowers the remaining
coordinates one by one using `lowerOthersAlong`.

This is the concrete regularity/monotonicity condition corresponding to the
paper's regularity lemma for permute-and-flip.
-/
theorem permuteAndFlipPMF_monotone
    {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hrr : q r ≤ q' r)
    (hothers : ∀ s : Fin n.succ, s ≠ r → q' s ≤ q s) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n q' ε₁ ε₂ r := by
  -- First move `q` to an intermediate vector `q1` that already has the correct
  -- value at coordinate `r`.
  let q1 : Scores n := bumpScore q r (q' r - q r)
  have hstep1 :
      permuteAndFlipPMF n q ε₁ ε₂ r ≤
        permuteAndFlipPMF n q1 ε₁ ε₂ r := by
    simpa [q1] using
      (permuteAndFlipPMF_bumpScore_self_ge q r (q' r - q r) ε₁ ε₂)
  have hothers1 :
      ∀ s : Fin n.succ, s ≠ r → q' s ≤ q1 s := by
    intro s hs
    simp [q1, bumpScore, hs, hothers s hs]
  have hstep2 :
      permuteAndFlipPMF n q1 ε₁ ε₂ r ≤
        permuteAndFlipPMF n (lowerOthersAlong (canonicalOrder n) q1 q' r) ε₁ ε₂ r := by
    -- Then lower every non-`r` coordinate, one by one, until reaching `q'`.
    -- `lowerOthersAlong` is just a proof device: it walks through the canonical
    -- list of all candidates and lowers each non-`r` coordinate exactly as much
    -- as needed, never touching `r`.
    exact lowerOthersAlong_le
      (canonicalOrder n)
      (by simpa [canonicalOrder] using List.nodup_finRange n.succ)
      q1 q' r ε₁ ε₂ hothers1
  have hrr1 : q1 r = q' r := by
    simp [q1, bumpScore, Nat.add_sub_of_le hrr]
  have hend :
      lowerOthersAlong (canonicalOrder n) q1 q' r = q' := by
    simpa using lowerOthersAlong_canonicalOrder_eq q1 q' r hrr1 hothers1
  calc
    permuteAndFlipPMF n q ε₁ ε₂ r
      ≤ permuteAndFlipPMF n q1 ε₁ ε₂ r := hstep1
    _ ≤ permuteAndFlipPMF n (lowerOthersAlong (canonicalOrder n) q1 q' r) ε₁ ε₂ r := hstep2
    _ = permuteAndFlipPMF n q' ε₁ ε₂ r := by simp [hend]

end Global

section PrivacyStep

/--
The paper's local privacy contraction for a single unit increase of `q r`.

This is a Lean formalization of the one-step recurrence/privacy inequality used in
the supplement's proof of Theorem 1 and related recurrence statements.
-/
theorem one_step_privacy
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ENNReal.ofReal (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂))) *
        permuteAndFlipPMF n (bumpScore q r 1) ε₁ ε₂ r ≤
      permuteAndFlipPMF n q ε₁ ε₂ r := by
  -- We split exactly as the paper does: either `r` is already maximal, or it
  -- is still below the maximum and the "easy" equality case applies.
  by_cases hgap : gap q r = 0
  · exact permuteAndFlipPMF_bumpScore_self_one_of_gap_zero q r ε₁ ε₂ hgap
  · have hlt : q r < maxScore q := by
      refine Nat.lt_of_not_ge ?_
      intro hge
      exact hgap (by simpa [gap_eq_maxScore_sub] using Nat.sub_eq_zero_of_le hge)
    have hstep : q r + 1 ≤ maxScore q := Nat.succ_le_of_lt hlt
    exact le_of_eq (by simpa using permuteAndFlipPMF_bumpScore_self_of_le q r 1 ε₁ ε₂ hstep)

/--
Iterating `one_step_privacy` yields the `k`-step contraction used in the final
range-distance theorem.
-/
theorem bumpScore_self_privacy_pow
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+) :
    (ENNReal.ofReal (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)))) ^ k *
        permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r ≤
      permuteAndFlipPMF n q ε₁ ε₂ r := by
  induction k generalizing q with
  | zero =>
      have hsame : bumpScore q r 0 = q := by
        funext i
        by_cases hi : i = r
        · subst hi
          simp [bumpScore]
        · simp [bumpScore, hi]
      simp [hsame]
  | succ k ih =>
      let α : ENNReal := ENNReal.ofReal (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)))
      have hstep :
          α * permuteAndFlipPMF n (bumpScore q r (k + 1)) ε₁ ε₂ r ≤
            permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r := by
        -- Apply the one-step theorem to the partially bumped score vector.
        -- This is the key inductive picture: compare the `k+1` vector to the
        -- `k` vector, not directly to the original `q`.
        simpa [α, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, bumpScore_add]
          using (one_step_privacy (q := bumpScore q r k) (r := r) (ε₁ := ε₁) (ε₂ := ε₂))
      calc
        (ENNReal.ofReal (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)))) ^ (k + 1) *
            permuteAndFlipPMF n (bumpScore q r (k + 1)) ε₁ ε₂ r
          = α ^ k * (α * permuteAndFlipPMF n (bumpScore q r (k + 1)) ε₁ ε₂ r) := by
              -- Rewrite the left-hand side so the one-step inequality can be
              -- applied inside a larger multiplicative context.
              simp [α, pow_succ']
              ac_rfl
        _ ≤ α ^ k * permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r := by
              exact mul_le_mul_right hstep (α ^ k)
        _ ≤ permuteAndFlipPMF n q ε₁ ε₂ r := by
              simpa [α] using ih (q := q)

end PrivacyStep

end PermuteAndFlip
end SLang
