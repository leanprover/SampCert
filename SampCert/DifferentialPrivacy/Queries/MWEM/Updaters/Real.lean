/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Queries.MWEM.Code

/-!
# Real-valued multiplicative-weights updater

Hardt's MWEM (Hardt, Ligett, McSherry 2012, Algorithm 1) with the synthetic
state in `Fin numBins → NNReal`. This is the textbook reference instantiation;
not extractable to executable code (uses `Real.exp` and real arithmetic).

Following Figure 1 of the paper:

* `A_0(x) = n / numBins` for all `x` (uniform with total mass `n`).
* The update for round `i` is
    `A_i(x) ∝ A_{i-1}(x) · exp( q_i(x) · (m_i - q_i(A_{i-1})) / (2n) )`
  with renormalization to fixed total `n`.

If the renormalization total degenerates to zero, the updater returns the zero
histogram. The privacy proof does not depend on non-degeneracy.
-/

noncomputable section

open Classical Nat Int Real ENNReal NNReal

namespace SLang

variable {numBins : ℕ+} {n : ℕ} {Δ : ℕ+}

def realLinearQuery (q : Fin numBins → ℤ) (D : List (Fin numBins)) : ℤ :=
  (D.map q).sum

def realLinearQueryReal (q : Fin numBins → ℤ) (A : Fin numBins → NNReal) : ℝ :=
  ∑ b, (q b : ℝ) * (A b : ℝ)

def realScore (q : Fin numBins → ℤ) (A : Fin numBins → NNReal) (D : List (Fin numBins)) : ℤ :=
  |realLinearQuery q D - ⌊realLinearQueryReal q A⌋|

def realMWUpdate (n : ℕ) (q : Fin numBins → ℤ) (m : ℤ) (A : Fin numBins → NNReal) :
    Fin numBins → NNReal :=
  let nR : ℝ := (n : ℝ)
  let err : ℝ := ((m : ℝ) - realLinearQueryReal q A) / (2 * nR)
  let unnorm : Fin numBins → ℝ := fun b => (A b : ℝ) * Real.exp ((q b : ℝ) * err)
  let total : ℝ := ∑ b, unnorm b
  fun b => Real.toNNReal (unnorm b * nR / total)

def realInit (n : ℕ) (numBins : ℕ+) : Fin numBins → NNReal :=
  fun _ => Real.toNNReal ((n : ℝ) / (numBins.val : ℝ))

theorem realLinearQuery_sens (q : Fin numBins → ℤ)
    (Hbound : ∀ b, |q b| ≤ (Δ : ℤ)) : sensitivity (realLinearQuery q) Δ := by
  intro l₁ l₂ Hn
  have qnat : ∀ k : Fin numBins, (q k).natAbs ≤ (Δ : ℕ) := fun k => by
    have := Hbound k; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  cases Hn with
  | @Addition a b k h1 h2 => subst h1 h2; simp [realLinearQuery]; exact qnat _
  | @Deletion a b k h1 h2 => subst h1 h2; simp [realLinearQuery]; exact qnat _

lemma natAbs_abs_sub_abs_le {a b : ℤ} : (|a| - |b|).natAbs ≤ (a - b).natAbs := by
  zify; exact abs_abs_sub_abs_le_abs_sub a b

theorem realScore_sens (q : Fin numBins → ℤ) (A : Fin numBins → NNReal)
    (Hbound : ∀ b, |q b| ≤ (Δ : ℤ)) : sensitivity (realScore q A) Δ := by
  intro l₁ l₂ Hn
  have hQ : (realLinearQuery q l₁ - realLinearQuery q l₂).natAbs ≤ (Δ : ℕ) :=
    realLinearQuery_sens (Δ := Δ) q Hbound l₁ l₂ Hn
  set c : ℤ := ⌊realLinearQueryReal q A⌋
  show (|realLinearQuery q l₁ - c| - |realLinearQuery q l₂ - c|).natAbs ≤ (Δ : ℕ)
  refine le_trans natAbs_abs_sub_abs_le ?_
  rw [show realLinearQuery q l₁ - c - (realLinearQuery q l₂ - c) =
        realLinearQuery q l₁ - realLinearQuery q l₂ from by ring]
  exact hQ

def realMWUpdater (nData : ℕ) (q : Fin (n+1) → Fin numBins → ℤ)
    (Hbound : ∀ i b, |q i b| ≤ (Δ : ℤ)) :
    SyntheticUpdater (Fin numBins) n Δ (Fin numBins → NNReal) (realInit nData numBins) where
  queries i := realLinearQuery (q i)
  scoreFn A i := realScore (q i) A
  update A i m := realMWUpdate nData (q i) m A
  queries_sens i := realLinearQuery_sens (q i) (Hbound i)
  scoreFn_sens A i := realScore_sens (q i) A (Hbound i)

end SLang

end
