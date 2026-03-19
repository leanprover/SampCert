import SampCert.DifferentialPrivacy.PermuteAndFlip.Range
import SampCert.DifferentialPrivacy.PermuteAndFlip.Monotonicity

/-!
Final privacy-facing theorems for permute-and-flip.

Main theorems in this file:
- `permuteAndFlipPMF_normalized_range_privacy`: normalized comparison after
  shifting score differences into a common natural interval
- `permuteAndFlipPMF_range_privacy`: final PMF privacy theorem
- `permuteAndFlipSLang_range_privacy`: exact-sampler refinement of the PMF theorem
-/

noncomputable section

namespace SLang
namespace PermuteAndFlip

/--
The per-unit privacy contraction factor `exp(-ε₁ / ε₂)` that appears throughout the
range-distance theorems below.
-/
def privacyBase (ε₁ : ℕ) (ε₂ : ℕ+) : ENNReal :=
  ENNReal.ofReal (Real.exp (- (((ε₁ : ℕ) : NNReal) / ε₂)))

/--
Normalized privacy comparison after shifting both score vectors into a common
natural-valued interval.

After normalization, the proof uses the `k`-step bump contraction and then
global monotonicity.
-/
theorem permuteAndFlipPMF_normalized_range_privacy
    {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    let B := RangePrivacy.upperEndpoint q q'
    let qshift : Scores n := fun i => q i + B
    let qtarget : Scores n := fun i => q i + RangePrivacy.shiftedDiff q q' i
    (privacyBase ε₁ ε₂) ^ rangeDistance q q' * permuteAndFlipPMF n qshift ε₁ ε₂ r ≤
      permuteAndFlipPMF n qtarget ε₁ ε₂ r := by
  let A := RangePrivacy.lowerEndpoint q q'
  let B := RangePrivacy.upperEndpoint q q'
  let qshift : Scores n := fun i => q i + B
  let qmid : Scores n := fun i => q i + if i = r then A else B
  let qtarget : Scores n := fun i => q i + RangePrivacy.shiftedDiff q q' i
  have hred :
      (privacyBase ε₁ ε₂) ^ rangeDistance q q' * permuteAndFlipPMF n qshift ε₁ ε₂ r ≤
        permuteAndFlipPMF n qmid ε₁ ε₂ r := by
    -- `qshift` is obtained from `qmid` by raising only candidate `r` by exactly
    -- the width of the normalized interval, so `bumpScore_self_privacy_pow` applies.
    have hbump : bumpScore qmid r (rangeDistance q q') = qshift := by
      funext i
      by_cases hi : i = r
      · subst hi
        simp [qmid, qshift, A, B, RangePrivacy.upperEndpoint_eq_lowerEndpoint_add_rangeDistance,
          bumpScore, Nat.add_assoc]
      · simp [qmid, qshift, bumpScore, hi]
    simpa [privacyBase, hbump] using
      (bumpScore_self_privacy_pow (q := qmid) (r := r) (k := rangeDistance q q')
        (ε₁ := ε₁) (ε₂ := ε₂))
  have hmono :
      permuteAndFlipPMF n qmid ε₁ ε₂ r ≤
        permuteAndFlipPMF n qtarget ε₁ ε₂ r := by
    -- After the bump step, every coordinate of `qtarget` lies between the same
    -- normalized endpoints, so global monotonicity finishes the comparison.
    apply permuteAndFlipPMF_monotone (q := qmid) (q' := qtarget) (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
    · have hle := RangePrivacy.lowerEndpoint_le_shiftedDiff q q' r
      simpa [qmid, qtarget, A] using Nat.add_le_add_left hle (q r)
    · intro s hsr
      have hle := RangePrivacy.shiftedDiff_le_upperEndpoint q q' s
      simpa [qmid, qtarget, B, hsr] using Nat.add_le_add_left hle (q s)
  exact le_trans hred hmono

/--
Final PMF privacy theorem for permute-and-flip under the range metric.

This is the development's main analogue of the paper's privacy theorem
(Theorem 1), phrased using `rangeDistance` instead of the paper's original
score-function presentation.
-/
theorem permuteAndFlipPMF_range_privacy
    {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    (privacyBase ε₁ ε₂) ^ rangeDistance q q' * permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n q' ε₁ ε₂ r := by
  -- Shift both score vectors so that their coordinatewise differences become a
  -- common natural-valued interval. The normalized theorem handles the real
  -- work, and shift-invariance transports the result back to the original scores.
  let B := RangePrivacy.upperEndpoint q q'
  let c := RangePrivacy.diffShift q q'
  let qshift : Scores n := fun i => q i + B
  let qtarget : Scores n := fun i => q i + RangePrivacy.shiftedDiff q q' i
  have htarget :
      qtarget = (fun i => q' i + c) := by
    -- By construction, `shiftedDiff` reconstructs `q'` up to a global shift.
    simpa [qtarget, c] using RangePrivacy.shiftedDiff_eq_targetShift q q'
  calc
    (privacyBase ε₁ ε₂) ^ rangeDistance q q' * permuteAndFlipPMF n q ε₁ ε₂ r
      = (privacyBase ε₁ ε₂) ^ rangeDistance q q' * permuteAndFlipPMF n qshift ε₁ ε₂ r := by
          -- Replace `q` by its globally shifted copy `qshift`.
          rw [permuteAndFlipPMF_shift (q := q) (c := B) (ε₁ := ε₁) (ε₂ := ε₂) (r := r)]
    _ ≤ permuteAndFlipPMF n qtarget ε₁ ε₂ r := by
          simpa [qshift, qtarget] using
            permuteAndFlipPMF_normalized_range_privacy (q := q) (q' := q') (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
    _ = permuteAndFlipPMF n q' ε₁ ε₂ r := by
          -- Remove the global shift on the target side.
          rw [htarget, permuteAndFlipPMF_shift (q := q') (c := c) (ε₁ := ε₁) (ε₂ := ε₂) (r := r)]

/--
Final PMF privacy theorem for permute-and-flip under the range metric.

This theorem is the `SLang` refinement of `permuteAndFlipPMF_range_privacy`.
-/
theorem permuteAndFlipSLang_range_privacy
    {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    (privacyBase ε₁ ε₂) ^ rangeDistance q q' * permuteAndFlipSLang n q ε₁ ε₂ r ≤
      permuteAndFlipSLang n q' ε₁ ε₂ r := by
  simpa [permuteAndFlipSLang_eq_permuteAndFlipPMF] using
    permuteAndFlipPMF_range_privacy q q' r ε₁ ε₂

end PermuteAndFlip
end SLang
