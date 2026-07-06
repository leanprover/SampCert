/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.SelectorCore

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace PermuteAndFlip
/-!
Permutation-averaged mechanism definitions built on top of selector-core lemmas.
-/

/--
The PMF-level permute-and-flip mechanism: draw a uniform random permutation of
the candidates, then run the fixed-order selector on that order.
-/
def permuteAndFlipPMF (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    PMF (Fin n.succ) := do
  let σ ← PMF.uniformOfFintype (Equiv.Perm (Fin n.succ))
  selectPMF ((canonicalOrder n).map σ) q ε₁ ε₂

/--
The executable `SLang` implementation of permute-and-flip, using the same
uniform permutation plus exact Bernoulli-exponential selector.
-/
def permuteAndFlipSLang (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    SLang (Fin n.succ) := do
  let σ ← ((PMF.uniformOfFintype (Equiv.Perm (Fin n.succ))) : SLang (Equiv.Perm (Fin n.succ)))
  selectSLang ((canonicalOrder n).map σ) q ε₁ ε₂

@[simp]
theorem permuteAndFlipSLang_eq_permuteAndFlipPMF
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    permuteAndFlipSLang n q ε₁ ε₂ = permuteAndFlipPMF n q ε₁ ε₂ := by
  ext i
  simp [permuteAndFlipSLang, permuteAndFlipPMF, selectSLang_eq_selectPMF]

@[simp]
theorem permuteAndFlipPMF_permute
    (n : CandidateCount) (τ : Equiv.Perm (Fin n.succ)) (q : Scores n)
    (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    permuteAndFlipPMF n (permuteScores τ q) ε₁ ε₂ (τ r) =
      permuteAndFlipPMF n q ε₁ ε₂ r := by
  -- Reindex the uniform sum over permutations by right-composition with `τ`.
  let e : Equiv.Perm (Equiv.Perm (Fin n.succ)) :=
    { toFun := fun σ => σ.trans τ
      invFun := fun σ => σ.trans τ.symm
      left_inv := by
        intro σ
        ext x
        simp
      right_inv := by
        intro σ
        ext x
        simp }
  simp [permuteAndFlipPMF, PMF.bind_apply]
  conv_lhs => rw [← Equiv.sum_comp e]
  apply Fintype.sum_congr
  intro σ
  simpa [e, Function.comp, PMF.uniformOfFintype_apply] using
    congrArg (fun x => (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) (e σ)) * x)
      (selectPMF_map_canonicalOrder_permute σ τ q ε₁ ε₂ r)

theorem permuteAndFlipPMF_eq_tsum_selectWeight
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    permuteAndFlipPMF n q ε₁ ε₂ r =
      ∑' σ : Equiv.Perm (Fin n.succ),
        PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
          selectWeight ((canonicalOrder n).map σ) q ε₁ ε₂ r := by
  -- Unfold the `bind` in `permuteAndFlipPMF` and replace the
  -- fixed-order selector PMF with the explicit weight formula from
  -- `SelectorCore`.
  simp [permuteAndFlipPMF, PMF.bind_apply, selectPMF_map_canonicalOrder_eq_selectWeight]

/--
This is the first closed form used later in the paper proof: factor out the
success probability of `r`, and average only the failure products over
candidates that appear before `r` in the sampled permutation.

This theorem is the executable-mechanism counterpart of the permutation-average formula
used in the paper's supplement before the inclusion-exclusion rewrite.
-/
theorem permuteAndFlipPMF_eq_coin_mul_tsum_beforeSet_prod
    (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (r : Fin n.succ) :
    permuteAndFlipPMF n q ε₁ ε₂ r =
      exactCoinPMF (gap q r * ε₁) ε₂ true *
        ∑' σ : Equiv.Perm (Fin n.succ),
          PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
            Finset.prod (beforeSet σ r) (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false) := by
  rw [permuteAndFlipPMF_eq_tsum_selectWeight]
  calc
    ∑' σ : Equiv.Perm (Fin n.succ),
        PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
          selectWeight ((canonicalOrder n).map σ) q ε₁ ε₂ r
      =
        ∑' σ : Equiv.Perm (Fin n.succ),
          PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
            (exactCoinPMF (gap q r * ε₁) ε₂ true *
              Finset.prod (beforeSet σ r) (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false)) := by
              -- Replace the fixed-order selector weight by its prefix-product formula.
              refine tsum_congr (fun σ => ?_)
              exact congrArg
                (fun x => PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ * x)
                (by
                  simpa [canonicalOrder] using
                    selectWeight_map_finRange_eq_coin_mul_beforeSet_prod σ q r ε₁ ε₂)
    _ =
        ∑' σ : Equiv.Perm (Fin n.succ),
          exactCoinPMF (gap q r * ε₁) ε₂ true *
            (PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
              Finset.prod (beforeSet σ r) (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false)) := by
              refine tsum_congr (fun σ => ?_)
              ac_rfl
    _ =
        exactCoinPMF (gap q r * ε₁) ε₂ true *
          ∑' σ : Equiv.Perm (Fin n.succ),
            PMF.uniformOfFintype (Equiv.Perm (Fin n.succ)) σ *
              Finset.prod (beforeSet σ r) (fun i => exactCoinPMF (gap q i * ε₁) ε₂ false) := by
              -- The factor involving `r` is independent of the sampled
              -- permutation, so it can be pulled completely outside the sum.
              rw [ENNReal.tsum_mul_left]


end PermuteAndFlip
end SLang
