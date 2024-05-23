/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.Foundations.Basic

noncomputable section

namespace SLang

abbrev Query (T U : Type) := List T → U
abbrev Mechanism (T U : Type) := List T → SLang U

def Compose (nq1 : Mechanism T U) (nq2 : Mechanism T V) (l : List T) : SLang (U × V) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

def PostProcess (nq : Mechanism T U) (pp : U → V) (l : List T) : SLang V := do
  let A ← nq l
  return pp A

class DPSystem (T : Type) where
  prop : Mechanism T Z → ℝ → Prop
  noise : Query T ℤ → ℕ+ → ℕ+ → ℕ+ → Mechanism T ℤ
  noise_prop : ∀ q : List T → ℤ, ∀ Δ εn εd : ℕ+, sensitivity q Δ → prop (noise q Δ εn εd) (εn / εd)
  compose_prop : {U V : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → [MeasurableSpace V] → [Countable V] → [DiscreteMeasurableSpace V] → [Inhabited V] → ∀ m₁ : Mechanism T U, ∀ m₂ : Mechanism T V, ∀ ε₁ ε₂ ε₃ ε₄ : ℕ+,
    prop m₁ (ε₁ / ε₂) → prop m₂ (ε₃ / ε₄) → prop (Compose m₁ m₂) ((ε₁ / ε₂) + (ε₃ / ε₄))
  postprocess_prop : {U : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → { pp : U → V } → Function.Surjective pp → ∀ m : Mechanism T U, ∀ ε₁ ε₂ : ℕ+,
   prop m (ε₁ / ε₂) → prop (PostProcess m pp) (ε₁ / ε₂)

def ComposeRW (nq1 : Mechanism T U) (nq2 : Mechanism T V) :
  Compose nq1 nq2 =
  fun l => do
    let A ← nq1 l
    let B ← nq2 l
    return (A,B) := by
  ext l x
  simp [Compose]

def PostProcessRW (nq : Mechanism T U) (pp : U → V) :
  PostProcess nq pp =
  fun l => do
    let A ← nq l
    return pp A := by
  ext l x
  simp [PostProcess]

@[simp]
theorem bind_bind_indep (p : Mechanism T U) (q : Mechanism T V) (h : U → V → SLang A)  :
  (fun l => (p l).bind (fun a : U => (q l).bind fun b : V => h a b))
    =
  fun l => (Compose p q l).bind (fun z => h z.1 z.2) := by
  ext l x
  simp [ComposeRW, tsum_prod']
  apply tsum_congr
  intro b
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro c
  rw [← mul_assoc]
  congr 1
  rw [tsum_eq_single b]
  . congr 1
    rw [tsum_eq_single c]
    . simp
    . intro b' h1
      simp
      intro h2
      subst h2
      contradiction
  . intro b' h1
    rw [tsum_eq_single c]
    . simp
      intro h2
      subst h2
      contradiction
    . intro b'' h2
      simp
      intro h3 h4
      subst h3
      subst h4
      contradiction

end SLang
