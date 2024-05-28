/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.Foundations.Basic

/-!
# Differential Privacy

This file defines a notion of a differential private system.

MARKUSDE: Check with JBT that I actually understand what he's doing here.
-/

noncomputable section

namespace SLang

abbrev Query (T U : Type) := List T → U
abbrev Mechanism (T U : Type) := List T → SLang U

/--
Product of mechanisms.

MARKUSDE: Doesn't "composition" imply the second one can depend on the first? As in Lemma 31 of "The Discrete Gaussian for Differential Privacy".
I think this should be named privSeq, the privacy bound composes, but the programs themselves are just sequenced.
-/
def privCompose (nq1 : Mechanism T U) (nq2 : Mechanism T V) (l : List T) : SLang (U × V) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

/--
Mechanism obtained by applying a post-processing function to a mechanism.
-/
def privPostProcess (nq : Mechanism T U) (pp : U → V) (l : List T) : SLang V := do
  let A ← nq l
  return pp A


/--
Abstract definition of a differentially private systemm.
-/
class DPSystem (T : Type) where
  /--
  Notion of differential privacy with a paramater (ε-DP, ε-zCDP, etc)
  -/
  prop : Mechanism T Z → ℝ → Prop
  /--
  Noise mechanism (eg. Laplace, Discrete Gaussian, etc)
  Paramaterized by a query, sensitivity, and the numerator/denominator ofa (rational) security paramater.
  -/
  noise : Query T ℤ → ℕ+ → ℕ+ → ℕ+ → Mechanism T ℤ
  /--
  Adding noise to a query makes it differentially private.
  -/
  noise_prop : ∀ q : List T → ℤ, ∀ Δ εn εd : ℕ+, sensitivity q Δ → prop (noise q Δ εn εd) (εn / εd)
  /--
  Notion of privacy composes by addition.
  -/
  compose_prop : {U V : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → [MeasurableSpace V] → [Countable V] → [DiscreteMeasurableSpace V] → [Inhabited V] → ∀ m₁ : Mechanism T U, ∀ m₂ : Mechanism T V, ∀ ε₁ ε₂ ε₃ ε₄ : ℕ+,
    prop m₁ (ε₁ / ε₂) → prop m₂ (ε₃ / ε₄) → prop (privCompose m₁ m₂) ((ε₁ / ε₂) + (ε₃ / ε₄))
  /--
  Notion of privacy is invariant under post-processing.
  -/
  postprocess_prop : {U : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → { pp : U → V } → Function.Surjective pp → ∀ m : Mechanism T U, ∀ ε₁ ε₂ : ℕ+,
   prop m (ε₁ / ε₂) → prop (privPostProcess m pp) (ε₁ / ε₂)

-- MARKUSDE: ??
def ComposeRW (nq1 : Mechanism T U) (nq2 : Mechanism T V) :
  privCompose nq1 nq2 =
  fun l => do
    let A ← nq1 l
    let B ← nq2 l
    return (A,B) := by
  ext l x
  simp [privCompose]

-- MARKUSDE: ??
def PostProcessRW (nq : Mechanism T U) (pp : U → V) :
  privPostProcess nq pp =
  fun l => do
    let A ← nq l
    return pp A := by
  ext l x
  simp [privPostProcess]

@[simp]
lemma bind_bind_indep (p : Mechanism T U) (q : Mechanism T V) (h : U → V → SLang A)  :
  (fun l => (p l).probBind (fun a : U => (q l).probBind fun b : V => h a b))
    =
  fun l => (privCompose p q l).probBind (fun z => h z.1 z.2) := by
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
