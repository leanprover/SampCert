/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Sensitivity

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
  postprocess_prop : {U : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → ∀ m : Mechanism T U, ∀ ε₁ ε₂ : ℕ+, ∀ pp : U → V, Function.Surjective pp →
   prop m (ε₁ / ε₂) → prop (PostProcess m pp) (ε₁ / ε₂)

end SLang
