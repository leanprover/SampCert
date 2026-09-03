/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System

/-!
# Report Noisy Max (Laplace variant)

Selection mechanism: given a finite, nonempty family of integer-valued queries
each of sensitivity `Δ`, draw independent discrete Laplace noise per query and
return the index of the largest noised score. This is `(ε₁/ε₂)`-DP independent
of the number of candidates.
-/

noncomputable section

namespace SLang

variable {T : Type}

/--
Sample independent Laplace noise for each of `n+1` queries, returning the joint
vector of noised values. Implemented as a fold over `Fin (n+1)`.
-/
def privNoisedFamily (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    PMF (Fin (n+1) → ℤ) :=
  match n with
  | 0 =>
    (privNoisedQueryPure (s 0) (2 * Δ) ε₁ ε₂ l).bind (fun z => PMF.pure (fun _ => z))
  | Nat.succ n' =>
    (privNoisedFamily n' (fun i => s i.castSucc) Δ ε₁ ε₂ l).bind (fun rest =>
      (privNoisedQueryPure (s (Fin.last (n'+1))) (2 * Δ) ε₁ ε₂ l).bind (fun last =>
        PMF.pure (fun i => if h : i.val < n'+1 then rest ⟨i.val, h⟩ else last)))

/--
Argmax of a function `Fin (n+1) → ℤ`, returning the largest `i` achieving the
maximum (ties broken by taking the larger index).
-/
def Fin.argmax (n : ℕ) (f : Fin (n+1) → ℤ) : Fin (n+1) :=
  match n with
  | 0 => 0
  | Nat.succ n' =>
    let prev := Fin.argmax n' (fun i => f i.castSucc)
    let last : Fin (n'+2) := Fin.last (n'+1)
    if f last < f prev.castSucc
      then prev.castSucc
      else last

/--
Report-Noisy-Max with discrete Laplace noise.

Given `n+1` candidate queries `s : Fin (n+1) → List T → ℤ` each of sensitivity
`Δ`, sample independent Laplace noise (scaled to `(2Δ * ε₂) / ε₁`) for each, and
return the index of the largest noised value.

The mechanism is `(ε₁/ε₂)`-DP regardless of `n`.
-/
def privReportNoisyMax (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    PMF (Fin (n+1)) :=
  (privNoisedFamily n s Δ ε₁ ε₂ l).bind (fun noised => PMF.pure (Fin.argmax n noised))

end SLang

end

namespace SLang

def privNoisedFamilySLang {T : Type} (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : SLang (Fin (n+1) → ℤ) :=
  match n with
  | 0 => do
    let z ← DiscreteLaplaceGenSample (2 * Δ * ε₂) ε₁ (s 0 l)
    return (fun _ => z)
  | Nat.succ n' => do
    let rest ← privNoisedFamilySLang n' (fun i => s i.castSucc) Δ ε₁ ε₂ l
    let last ← DiscreteLaplaceGenSample (2 * Δ * ε₂) ε₁ (s (Fin.last (n'+1)) l)
    return (fun i => if h : i.val < n'+1 then rest ⟨i.val, h⟩ else last)

def privReportNoisyMaxSLang {T : Type} (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : SLang (Fin (n+1)) := do
  let noised ← privNoisedFamilySLang n s Δ ε₁ ε₂ l
  return Fin.argmax n noised

theorem privNoisedFamilySLang_eq {T : Type} (n : ℕ) (s : Fin (n+1) → List T → ℤ)
    (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedFamilySLang n s Δ ε₁ ε₂ l = ((privNoisedFamily n s Δ ε₁ ε₂ l : PMF _) : SLang _) := by
  induction n with
  | zero =>
    show probBind (DiscreteLaplaceGenSample (2 * Δ * ε₂) ε₁ (s 0 l))
           (fun z => probPure (fun _ => z)) = _
    rfl
  | succ n IH =>
    show probBind (privNoisedFamilySLang n _ Δ ε₁ ε₂ l) _ = _
    rw [IH]
    rfl

theorem privReportNoisyMaxSLang_eq {T : Type} (n : ℕ) (s : Fin (n+1) → List T → ℤ)
    (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privReportNoisyMaxSLang n s Δ ε₁ ε₂ l =
      ((privReportNoisyMax n s Δ ε₁ ε₂ l : PMF _) : SLang _) := by
  show probBind (privNoisedFamilySLang n s Δ ε₁ ε₂ l) _ = _
  rw [privNoisedFamilySLang_eq]
  rfl

def privReportNoisyMaxSPMF {T : Type} (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : SPMF (Fin (n+1)) :=
  ⟨ privReportNoisyMaxSLang n s Δ ε₁ ε₂ l,
    privReportNoisyMaxSLang_eq n s Δ ε₁ ε₂ l ▸ (privReportNoisyMax n s Δ ε₁ ε₂ l).2 ⟩

end SLang
