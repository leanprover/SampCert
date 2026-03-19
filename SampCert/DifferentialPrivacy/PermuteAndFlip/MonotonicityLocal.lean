import SampCert.DifferentialPrivacy.PermuteAndFlip.Paper.ClosedForm

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
Local monotonicity lemmas for raising the selected score and lowering competing scores.

This file contains the one-coordinate inequalities that power the global
monotonicity argument in [Monotonicity](SampCert/DifferentialPrivacy/PermuteAndFlip/Monotonicity.lean).
-/

/-! ### Raising the selected candidate -/

theorem permuteAndFlipPMF_bumpScore_self_of_le
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hmax : q r + k ≤ maxScore q) :
    ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
        permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r =
      permuteAndFlipPMF n q ε₁ ε₂ r := by
  have hterm (σ : Equiv.Perm (Fin n.succ)) :
      ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
          (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
            selectPMF ((canonicalOrder n).map σ) (bumpScore q r k) ε₁ ε₂ r)
        =
      PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
        selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r := by
    calc
      ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
          (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
            selectPMF ((canonicalOrder n).map σ) (bumpScore q r k) ε₁ ε₂ r)
        = PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
            (ENNReal.ofReal (Real.exp (- (((k * ε₁ : ℕ) : NNReal) / ε₂))) *
              selectPMF ((canonicalOrder n).map σ) (bumpScore q r k) ε₁ ε₂ r) := by
                ac_rfl
      _ = PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
            selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂ r := by
              -- The selector-level equality is lifted into one term of the
              -- outer permutation average.
              exact congrArg
                (fun x => PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ * x)
                (selectPMF_bumpScore_self_of_le_map_canonicalOrder σ q r k ε₁ ε₂ hmax)
  simp [permuteAndFlipPMF, PMF.bind_apply]
  -- Summing the fixed-permutation equalities over all permutations yields the
  -- full PMF statement.
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun σ => ?_)
  simpa [PMF.uniformOfFintype_apply] using hterm σ

theorem permuteAndFlipPMF_bumpScore_self_of_gap_zero_le
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hgap : gap q r = 0) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r := by
  simp [permuteAndFlipPMF, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro σ
  exact mul_le_mul' le_rfl
    (selectPMF_bumpScore_self_of_gap_zero_le_map_canonicalOrder σ q r k ε₁ ε₂ hgap)

theorem permuteAndFlipPMF_lowerScore_other_of_max_eq_le
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) (hk : k ≤ q s)
    (hmax : maxScore (lowerScore q s k) = maxScore q) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (lowerScore q s k) ε₁ ε₂ r := by
  simp [permuteAndFlipPMF, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro σ
  exact mul_le_mul' le_rfl
    (selectPMF_lowerScore_other_of_max_eq_le_map_canonicalOrder σ q r s k ε₁ ε₂ hrs hk hmax)

/-! ### Lowering a competing candidate -/

theorem maxScore_lowerScore_of_exists_other_argmax
    {n : CandidateCount} (q : Scores n) (s : Fin n.succ) (k : ℕ)
    (hk : k ≤ q s)
    (hother : ∃ t : Fin n.succ, t ≠ s ∧ q t = maxScore q) :
    maxScore (lowerScore q s k) = maxScore q := by
  rcases hother with ⟨t, hts, htmax⟩
  refine le_antisymm ?_ ?_
  · unfold maxScore lowerScore
    -- Lowering one coordinate cannot push any value above the old maximum.
    refine Finset.sup_le ?_
    intro i
    by_cases his : i = s
    · subst his
      have hqi : q i ≤ maxScore q := Finset.le_sup (s := Finset.univ) (f := q) (by simp)
      simpa [lowerScore] using le_trans (Nat.sub_le (q i) k) hqi
    · have hqi : q i ≤ maxScore q := Finset.le_sup (s := Finset.univ) (f := q) (by simp)
      simpa [lowerScore, his] using hqi
  · rw [← htmax]
    unfold maxScore lowerScore
    -- The witness `t` keeps the old maximum alive after lowering `s`, because
    -- `t` is a different maximizing coordinate and is therefore untouched.
    simpa [lowerScore, hts] using
      (Finset.le_sup (s := Finset.univ) (f := fun i => q i - if i = s then k else 0) (by simp : t ∈ Finset.univ))

theorem permuteAndFlipPMF_lowerScore_nonunique_max_le
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) (hk : k ≤ q s)
    (hother : ∃ t : Fin n.succ, t ≠ s ∧ q t = maxScore q) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (lowerScore q s k) ε₁ ε₂ r := by
  apply permuteAndFlipPMF_lowerScore_other_of_max_eq_le q r s k ε₁ ε₂ hrs hk
  exact maxScore_lowerScore_of_exists_other_argmax q s k hk hother

theorem permuteAndFlipPMF_lowerScore_unique_max_one_le
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s)
    (huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (lowerScore q s 1) ε₁ ε₂ r := by
  -- This is the delicate local monotonicity step. When `s` is the
  -- unique maximizer, lowering it changes the global maximum, so we switch to
  -- the paper's closed form and prove the comparison analytically there.
  let ρ : ℝ := Real.exp (- ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ))
  have hρ0 : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    have hnonneg : (0 : ℝ) ≤ ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by positivity
    simpa using Real.exp_le_exp.mpr (by linarith : -(((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) ≤ 0)
  have hgap' : gap (lowerScore q s 1) s = 0 := by
    rw [gap_eq_maxScore_sub, maxScore_lowerScore_unique_max_one q s huniq]
    simp [lowerScore]
  rw [permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt n q ε₁ ε₂ r]
  rw [permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt n (lowerScore q s 1) ε₁ ε₂ r]
  apply ENNReal.ofReal_le_ofReal
  have hprob :
      paperProb q ε₁ ε₂ r =
        ρ * paperProb (lowerScore q s 1) ε₁ ε₂ r := by
    simpa [ρ] using paperProb_lowerScore_other_of_unique_max_one q s r ε₁ ε₂ hrs huniq
  have halt :
      paperAlt q r ε₁ ε₂ =
        paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂ ρ := by
    simpa [ρ] using
      paperAlt_eq_paperAltGapZeroScaled_lowerScore_unique_max_one q r s ε₁ ε₂ hrs huniq
  have hscaled :
      ρ * paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂ ρ ≤
        paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂ 1 := by
    exact paperAltGapZeroScaled_mul_le_paperAltGapZero
      (q := lowerScore q s 1) (r := r) (s := s) (ε₁ := ε₁) (ε₂ := ε₂) hρ0 hρ1
  have hprob_nonneg : 0 ≤ paperProb (lowerScore q s 1) ε₁ ε₂ r := by
    unfold paperProb
    positivity
  have halt' :
      paperAlt (lowerScore q s 1) r ε₁ ε₂ =
        paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂ 1 := by
    exact paperAlt_eq_paperAltGapZeroScaled_one
      (q := lowerScore q s 1) (r := r) (s := s) (ε₁ := ε₁) (ε₂ := ε₂) hrs.symm hgap'
  calc
    -- Rewrite both PMFs in the paper's closed form. After that, the proof is a
    -- scalar inequality: one factor rescales exactly by `ρ`, and the remaining
    -- reduced polynomial is monotone in the scaling parameter.
    paperProb q ε₁ ε₂ r * paperAlt q r ε₁ ε₂
      = paperProb (lowerScore q s 1) ε₁ ε₂ r *
          (ρ * paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂ ρ) := by
            rw [hprob, halt]
            ring
    _ ≤ paperProb (lowerScore q s 1) ε₁ ε₂ r *
          paperAltGapZeroScaled (lowerScore q s 1) r s ε₁ ε₂ 1 := by
            exact mul_le_mul_of_nonneg_left hscaled hprob_nonneg
    _ = paperProb (lowerScore q s 1) ε₁ ε₂ r *
          paperAlt (lowerScore q s 1) r ε₁ ε₂ := by
            rw [halt']

theorem permuteAndFlipPMF_lowerScore_other_one_le
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (lowerScore q s 1) ε₁ ε₂ r := by
  by_cases hother : ∃ t : Fin n.succ, t ≠ s ∧ q t = maxScore q
  · -- If `s` is not uniquely maximal, lowering it preserves the maximum score,
    -- so the easy local monotonicity lemma applies.
    by_cases hqs : 1 ≤ q s
    · exact permuteAndFlipPMF_lowerScore_nonunique_max_le q r s 1 ε₁ ε₂ hrs hqs hother
    · have hs0 : q s = 0 := by omega
      have hsame : lowerScore q s 1 = q := by
        funext i
        by_cases his : i = s
        · subst his
          simp [lowerScore, hs0]
        · simp [lowerScore, his]
      simp [hsame]
  · -- Otherwise `s` is the unique maximizer, which is exactly the analytic
    -- branch handled by `permuteAndFlipPMF_lowerScore_unique_max_one_le`.
    have hsmax : q s = maxScore q := by
      by_cases hs : q s = maxScore q
      · exact hs
      · obtain ⟨t, ht⟩ := exists_argmax q
        have hts : t ≠ s := by
          intro hts'
          apply hs
          simpa [hts'] using ht
        exact False.elim (hother ⟨t, hts, ht⟩)
    have huniq : ∀ t : Fin n.succ, t ≠ s → q t < q s := by
      intro t hts
      have hle : q t ≤ maxScore q := Finset.le_sup (s := Finset.univ) (f := q) (by simp)
      have hne : q t ≠ maxScore q := by
        intro ht
        exact hother ⟨t, hts, ht⟩
      rw [hsmax]
      exact lt_of_le_of_ne hle hne
    exact permuteAndFlipPMF_lowerScore_unique_max_one_le q r s ε₁ ε₂ hrs huniq

/-! ### Iterating one-coordinate updates -/

theorem permuteAndFlipPMF_lowerScore_other_le
    {n : CandidateCount} (q : Scores n) (r s : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+)
    (hrs : r ≠ s) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (lowerScore q s k) ε₁ ε₂ r := by
  induction k generalizing q with
  | zero =>
      have hsame : lowerScore q s 0 = q := by
        funext i
        by_cases hi : i = s
        · subst hi
          simp [lowerScore]
        · simp [lowerScore, hi]
      simp [hsame]
  | succ k ih =>
      calc
        permuteAndFlipPMF n q ε₁ ε₂ r
          ≤ permuteAndFlipPMF n (lowerScore q s k) ε₁ ε₂ r := ih q
        _ ≤ permuteAndFlipPMF n (lowerScore (lowerScore q s k) s 1) ε₁ ε₂ r :=
              -- Peel off one unit at a time so the local one-step theorem can
              -- be reused uniformly.
              permuteAndFlipPMF_lowerScore_other_one_le (q := lowerScore q s k) (r := r) (s := s) (ε₁ := ε₁) (ε₂ := ε₂) hrs
        _ = permuteAndFlipPMF n (lowerScore q s (k + 1)) ε₁ ε₂ r := by
              rw [lowerScore_add]

theorem permuteAndFlipPMF_bumpScore_self_one_ge
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (bumpScore q r 1) ε₁ ε₂ r := by
  -- Again there are two branches: if `r` is already maximal, raising it can
  -- only help; otherwise we use the exact equality from the easy case and
  -- discard the extra multiplicative privacy factor.
  by_cases hgap : gap q r = 0
  · exact permuteAndFlipPMF_bumpScore_self_of_gap_zero_le q r 1 ε₁ ε₂ hgap
  · have hlt : q r < maxScore q := by
      refine Nat.lt_of_not_ge ?_
      intro hge
      exact hgap (by simpa [gap_eq_maxScore_sub] using Nat.sub_eq_zero_of_le hge)
    have hstep : q r + 1 ≤ maxScore q := Nat.succ_le_of_lt hlt
    have heq := permuteAndFlipPMF_bumpScore_self_of_le q r 1 ε₁ ε₂ hstep
    have hα1 : Real.exp (- ((((1 * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) ≤ 1 := by
      have hnonneg : (0 : ℝ) ≤ ((((1 * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ) := by positivity
      simpa using Real.exp_le_exp.mpr (by linarith : -(((((1 * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)) ≤ 0)
    have hmul :
        ENNReal.ofReal (Real.exp (- ((((1 * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ))) *
          permuteAndFlipPMF n (bumpScore q r 1) ε₁ ε₂ r
          ≤ permuteAndFlipPMF n (bumpScore q r 1) ε₁ ε₂ r := by
      -- The privacy factor is at most `1`, so dropping it turns the exact
      -- equality into the monotonicity inequality we want here.
      have hαENN :
          ENNReal.ofReal (Real.exp (- ((((1 * ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ))) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal hα1
      exact mul_le_of_le_one_left' hαENN
    exact heq ▸ hmul

theorem permuteAndFlipPMF_bumpScore_self_ge
    {n : CandidateCount} (q : Scores n) (r : Fin n.succ) (k ε₁ : ℕ) (ε₂ : ℕ+) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r := by
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
      calc
        permuteAndFlipPMF n q ε₁ ε₂ r
          ≤ permuteAndFlipPMF n (bumpScore q r k) ε₁ ε₂ r := ih q
        _ ≤ permuteAndFlipPMF n (bumpScore (bumpScore q r k) r 1) ε₁ ε₂ r :=
              -- As in the lowering proof, iterate the one-step statement.
              permuteAndFlipPMF_bumpScore_self_one_ge (q := bumpScore q r k) (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
        _ = permuteAndFlipPMF n (bumpScore q r (k + 1)) ε₁ ε₂ r := by
              rw [bumpScore_add]

theorem lowerOthersAlong_le
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q q' : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hothers : ∀ s : Fin n.succ, s ≠ r → q' s ≤ q s) :
    permuteAndFlipPMF n q ε₁ ε₂ r ≤
      permuteAndFlipPMF n (lowerOthersAlong l q q' r) ε₁ ε₂ r := by
  induction l generalizing q with
  | nil =>
      simp [lowerOthersAlong]
  | cons s l ih =>
      simp at hl
      rcases hl with ⟨_hs_not_mem, hl⟩
      by_cases hsr : s = r
      · simp [lowerOthersAlong, hsr]
        exact ih hl q hothers
      · have hstep :
            permuteAndFlipPMF n q ε₁ ε₂ r ≤
              permuteAndFlipPMF n (lowerScore q s (q s - q' s)) ε₁ ε₂ r := by
            -- Lower the current coordinate `s` all the way down to its target
            -- value `q' s`.
            exact permuteAndFlipPMF_lowerScore_other_le
              (q := q) (r := r) (s := s) (k := q s - q' s) (ε₁ := ε₁) (ε₂ := ε₂)
              (by intro h; exact hsr h.symm)
        have hothers' :
            ∀ t : Fin n.succ, t ≠ r → q' t ≤ (lowerScore q s (q s - q' s)) t := by
          intro t htr
          by_cases hts : t = s
          · have hsle : q' t ≤ q t := hothers t htr
            rw [show (lowerScore q s (q s - q' s)) t = q t - (q t - q' t) by
                  simp [lowerScore, hts]]
            omega
          · simp [lowerScore, hts]
            exact hothers t htr
        have htail :=
          ih hl (lowerScore q s (q s - q' s)) hothers'
        -- Compose the one-coordinate step with the inductive hypothesis on the
        -- remaining tail of the list.
        simpa [lowerOthersAlong, hsr] using le_trans hstep htail

theorem lowerOthersAlong_apply_of_not_mem
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q q' : Scores n) (r i : Fin n.succ)
    (hi : i ∉ l) :
    lowerOthersAlong l q q' r i = q i := by
  induction l generalizing q with
  | nil =>
      simp [lowerOthersAlong]
  | cons s l ih =>
      simp at hl
      rcases hl with ⟨_hs_not_mem, hl⟩
      have hi' : i ∉ l := by
        intro hil
        exact hi (by simp [hil])
      by_cases hsr : s = r
      · simpa [lowerOthersAlong, hsr] using ih hl q hi'
      · have his : i ≠ s := by
          intro his
          exact hi (by simp [his])
        simpa [lowerOthersAlong, hsr, lowerScore, his] using
          (ih hl (lowerScore q s (q s - q' s)) hi')

theorem lowerOthersAlong_apply_of_mem
    {n : CandidateCount} (l : List (Fin n.succ)) (hl : l.Nodup)
    (q q' : Scores n) (r i : Fin n.succ)
    (hothers : ∀ s : Fin n.succ, s ≠ r → q' s ≤ q s)
    (hi : i ∈ l) :
    lowerOthersAlong l q q' r i = if i = r then q i else q' i := by
  induction l generalizing q with
  | nil =>
      cases hi
  | cons s l ih =>
      simp at hl
      rcases hl with ⟨hs_not_mem, hl⟩
      simp at hi
      by_cases hsr : s = r
      · rcases hi with rfl | hi
        · have hr_not_mem : r ∉ l := by
              simpa [← hsr] using hs_not_mem
          have htail :
              lowerOthersAlong l q q' r r = q r := by
            exact lowerOthersAlong_apply_of_not_mem l hl q q' r r hr_not_mem
          simpa [lowerOthersAlong, hsr]
            using htail
        · have hir : i ≠ r := by
            intro hir
            exact hs_not_mem (by simpa [hsr, hir] using hi)
          simpa [lowerOthersAlong, hsr, hir] using ih hl q hothers hi
      · cases hi with
        | inl his =>
            have hsle : q' s ≤ q s := hothers s (by simpa using hsr)
            have htail :
                lowerOthersAlong l (lowerScore q s (q s - q' s)) q' r s =
                  (lowerScore q s (q s - q' s)) s := by
              exact lowerOthersAlong_apply_of_not_mem l hl (lowerScore q s (q s - q' s)) q' r s hs_not_mem
            calc
              lowerOthersAlong (s :: l) q q' r i
                = lowerOthersAlong l (lowerScore q s (q s - q' s)) q' r s := by
                    simp [his, lowerOthersAlong, hsr]
              _ = (lowerScore q s (q s - q' s)) s := htail
              _ = q' s := by
                    have hsub : q s - (q s - q' s) = q' s := by omega
                    simp [lowerScore, hsub]
              _ = if i = r then q i else q' i := by
                    subst his
                    simp [lowerOthersAlong, hsr]
        | inr hi =>
            have his : i ≠ s := by
              intro his
              exact hs_not_mem (by simpa [his] using hi)
            have hothers' :
                ∀ t : Fin n.succ, t ≠ r → q' t ≤ (lowerScore q s (q s - q' s)) t := by
              intro t htr
              by_cases hts : t = s
              · have hsle : q' t ≤ q t := hothers t htr
                rw [show (lowerScore q s (q s - q' s)) t = q t - (q t - q' t) by
                      simp [lowerScore, hts]]
                omega
              · simp [lowerScore, hts]
                exact hothers t htr
            have htail := ih hl (lowerScore q s (q s - q' s)) hothers' hi
            by_cases hir : i = r
            · calc
                lowerOthersAlong (s :: l) q q' r i
                  = lowerOthersAlong l (lowerScore q s (q s - q' s)) q' r i := by
                      simp [lowerOthersAlong, hsr]
                _ = (lowerScore q s (q s - q' s)) i := by
                      simpa [hir] using htail
                _ = q i := by
                      simp [lowerScore, his]
                _ = if i = r then q i else q' i := by
                      simp [hir]
            · calc
                lowerOthersAlong (s :: l) q q' r i
                  = lowerOthersAlong l (lowerScore q s (q s - q' s)) q' r i := by
                      simp [lowerOthersAlong, hsr]
                _ = if i = r then (lowerScore q s (q s - q' s)) i else q' i := htail
                _ = q' i := by
                      simp [hir]
                _ = if i = r then q i else q' i := by
                      simp [hir]

theorem lowerOthersAlong_canonicalOrder_eq
    {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ)
    (hrr : q r = q' r)
    (hothers : ∀ s : Fin n.succ, s ≠ r → q' s ≤ q s) :
    lowerOthersAlong (canonicalOrder n) q q' r = q' := by
  funext i
  -- Every coordinate appears exactly once in the canonical order, so the
  -- pointwise description from `lowerOthersAlong_apply_of_mem` is enough.
  have hi : i ∈ canonicalOrder n := by
    simp [canonicalOrder]
  have hl : (canonicalOrder n).Nodup := by
    simpa [canonicalOrder] using List.nodup_finRange n.succ
  rw [lowerOthersAlong_apply_of_mem (canonicalOrder n) hl q q' r i hothers hi]
  by_cases hir : i = r
  · subst hir
    simp [hrr]
  · simp [hir]

end PermuteAndFlip
end SLang
