/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Queries.MWEM.Code

/-!
# Float-valued multiplicative-weights updater

Hardt's MWEM (Hardt, Ligett, McSherry 2012, Algorithm 1) with the synthetic
state implemented in IEEE-754 doubles. This is the representation used by
deployed systems (SmartNoise, etc.).

The synthetic state lives in `Fin numBins → Float`. Following Figure 1 of the
paper:

* `A_0` is the uniform distribution scaled by `n` (dataset size), so each bin
  starts with mass `n / numBins` and the total is `n`.
* The update rule for each round `i` is
    `A_i(x) ∝ A_{i-1}(x) · exp( q_i(x) · (m_i - q_i(A_{i-1})) / (2n) )`
  with renormalization to fixed total `n`.

Privacy comes from the Laplace mechanism in the measurement step, which uses
exact integer arithmetic. The Float update is post-processing of the integer
transcript and contributes no privacy cost. Lean's Float type has essentially
no axiomatic theory, but the privacy proof requires only that the update be a
total function of its arguments.

The score function uses `Float.toInt32` to produce an integer constant (in `D`)
for sensitivity reasons; its specific value depends on IEEE-754 semantics but
is irrelevant to the sensitivity bound.
-/

open Classical Nat Int Real ENNReal

namespace SLang

variable {numBins : ℕ+} {n : ℕ} {Δ : ℕ+}

def intToFloat (n : ℤ) : Float :=
  match n with
  | .ofNat k => k.toUInt64.toFloat
  | .negSucc k => -((k + 1).toUInt64.toFloat)

def floatToInt (x : Float) : ℤ := x.toInt32.toInt

def floatLinearQuery (q : Fin numBins → ℤ) (D : List (Fin numBins)) : ℤ :=
  (D.map q).sum

def floatLinearQueryFloat (q : Fin numBins → ℤ) (A : Fin numBins → Float) : Float :=
  ((List.finRange numBins).map (fun b => intToFloat (q b) * A b)).foldr (· + ·) 0.0

def floatScore (q : Fin numBins → ℤ) (A : Fin numBins → Float) (D : List (Fin numBins)) : ℤ :=
  |floatLinearQuery q D - floatToInt (floatLinearQueryFloat q A)|

def floatMWUpdate (n : ℕ) (q : Fin numBins → ℤ) (m : ℤ) (A : Fin numBins → Float) :
    Fin numBins → Float :=
  let nF : Float := intToFloat (n : ℤ)
  let err : Float := (intToFloat m - floatLinearQueryFloat q A) / (2.0 * nF)
  let unnorm : Fin numBins → Float := fun b => A b * Float.exp (intToFloat (q b) * err)
  let total : Float :=
    ((List.finRange numBins).map unnorm).foldr (· + ·) 0.0
  fun b => unnorm b * nF / total

def floatInit (n : ℕ) (numBins : ℕ+) : Fin numBins → Float :=
  fun _ => intToFloat (n : ℤ) / intToFloat (numBins.val : ℤ)

theorem floatLinearQuery_sens (q : Fin numBins → ℤ)
    (Hbound : ∀ b, |q b| ≤ (Δ : ℤ)) : sensitivity (floatLinearQuery q) Δ := by
  intro l₁ l₂ Hn
  have qnat : ∀ k : Fin numBins, (q k).natAbs ≤ (Δ : ℕ) := fun k => by
    have := Hbound k; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  cases Hn with
  | @Addition a b k h1 h2 => subst h1 h2; simp [floatLinearQuery]; exact qnat _
  | @Deletion a b k h1 h2 => subst h1 h2; simp [floatLinearQuery]; exact qnat _

lemma natAbs_abs_sub_abs_le' {a b : ℤ} : (|a| - |b|).natAbs ≤ (a - b).natAbs := by
  zify; exact abs_abs_sub_abs_le_abs_sub a b

theorem floatScore_sens (q : Fin numBins → ℤ) (A : Fin numBins → Float)
    (Hbound : ∀ b, |q b| ≤ (Δ : ℤ)) : sensitivity (floatScore q A) Δ := by
  intro l₁ l₂ Hn
  have hQ : (floatLinearQuery q l₁ - floatLinearQuery q l₂).natAbs ≤ (Δ : ℕ) :=
    floatLinearQuery_sens (Δ := Δ) q Hbound l₁ l₂ Hn
  set c : ℤ := floatToInt (floatLinearQueryFloat q A)
  show (|floatLinearQuery q l₁ - c| - |floatLinearQuery q l₂ - c|).natAbs ≤ (Δ : ℕ)
  refine le_trans natAbs_abs_sub_abs_le' ?_
  rw [show floatLinearQuery q l₁ - c - (floatLinearQuery q l₂ - c) =
        floatLinearQuery q l₁ - floatLinearQuery q l₂ from by ring]
  exact hQ

def floatMWUpdater (nData : ℕ) (q : Fin (n+1) → Fin numBins → ℤ)
    (Hbound : ∀ i b, |q i b| ≤ (Δ : ℤ)) :
    SyntheticUpdater (Fin numBins) n Δ (Fin numBins → Float) (floatInit nData numBins) where
  queries i := floatLinearQuery (q i)
  scoreFn A i := floatScore (q i) A
  update A i m := floatMWUpdate nData (q i) m A
  queries_sens i := floatLinearQuery_sens (q i) (Hbound i)
  scoreFn_sens A i := floatScore_sens (q i) A (Hbound i)

end SLang
