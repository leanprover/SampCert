/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Generic
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.Foundations.Basic
import SampCert.DifferentialPrivacy.Approximate.DP

/-!
# Differential Privacy

This file defines an abstract system of differentially private operators.
-/

open Classical Nat Int Real ENNReal

namespace SLang

/--
Typeclass synonym for the classes we use for probaility
-/
class DiscProbSpace (T : Type) where
  instMeasurableSpace : MeasurableSpace T
  instCountable : Countable T
  instDiscreteMeasurableSpace : DiscreteMeasurableSpace T
  instInhabited : Inhabited T

-- Typeclass inference to- and from- the synonym
instance [idps : DiscProbSpace T] : MeasurableSpace T := idps.instMeasurableSpace
instance [idps : DiscProbSpace T] : Countable T := idps.instCountable
instance [idps : DiscProbSpace T] : DiscreteMeasurableSpace T := idps.instDiscreteMeasurableSpace
instance [idps : DiscProbSpace T] : Inhabited T := idps.instInhabited

instance [im : MeasurableSpace T] [ic : Countable T] [idm : DiscreteMeasurableSpace T] [ii : Inhabited T] : DiscProbSpace T where
  instMeasurableSpace := im
  instCountable := ic
  instDiscreteMeasurableSpace := idm
  instInhabited := ii

/--
Abstract definition of a differentially private systemm.
-/
class DPSystem (T : Type) where
  /--
  Differential privacy proposition, with one real parameter (ε-DP, ε-zCDP, etc)
  -/
  prop : Mechanism T Z → NNReal → Prop

  /--
  Definition of DP is well-formed: Privacy parameter required to obtain (ε', δ)-approximate DP
  -/
  of_app_dp : (δ : NNReal) -> (ε' : NNReal) -> NNReal
  /--
  For any ε', this definition of DP implies (ε', δ)-approximate-DP for all δ
  -/
  prop_adp [DiscProbSpace Z] {m : Mechanism T Z} : ∀ (δ : NNReal) (_ : 0 < δ) (ε' : NNReal),
    (prop m (of_app_dp δ ε') -> ApproximateDP m ε' δ)
  /--
  DP is monotonic
  -/
  prop_mono {m : Mechanism T Z} {ε₁ ε₂: NNReal} :
    ε₁ ≤ ε₂ -> prop m ε₁ -> prop m ε₂
  /--
  Privacy adaptively composes by addition.
  -/
  adaptive_compose_prop {U V : Type} [DiscProbSpace U] [DiscProbSpace V]
    {m₁ : Mechanism T U} {m₂ : U -> Mechanism T V} {ε₁ ε₂ ε : NNReal} :
    prop m₁ ε₁ → (∀ u, prop (m₂ u) ε₂) ->
    ε₁ + ε₂ = ε ->
    prop (privComposeAdaptive m₁ m₂) ε
  /--
  Privacy is invariant under post-processing.
  -/
  postprocess_prop {U : Type} [DiscProbSpace U]
    { pp : U → V } {m : Mechanism T U} {ε : NNReal} :
    prop m ε → prop (privPostProcess m pp) ε
  /--
  Constant query is 0-DP
  -/
  const_prop {U : Type} [DiscProbSpace U] {u : U} {ε : NNReal} :
    ε = (0 : NNReal) -> prop (privConst u) ε

namespace DPSystem

/-
Non-adaptive privacy composes by addition.
-/
lemma compose_prop {U V : Type} [dps : DPSystem T] [DiscProbSpace U] [DiscProbSpace V] :
    {m₁ : Mechanism T U} -> {m₂ : Mechanism T V} ->  {ε₁ ε₂ ε : NNReal} ->
    (ε₁ + ε₂ = ε) ->
    dps.prop m₁ ε₁ → dps.prop m₂ ε₂ → dps.prop (privCompose m₁ m₂) ε := by
  intros _ _ _ _ _ _ p1 p2
  unfold privCompose
  apply adaptive_compose_prop p1 (fun _ => p2)
  trivial

end DPSystem


lemma DPSystem_prop_ext [dps : DPSystem T] {ε₁ ε₂ : NNReal} (m : Mechanism T U) (Hε : ε₁ = ε₂) (H : dps.prop m ε₁) :
    dps.prop m ε₂ := by
  rw [<- Hε]
  assumption


@[simp]
lemma bind_bind_indep (p : Mechanism T U) (q : Mechanism T V) (h : U → V → PMF A) :
    (fun l => (p l) >>= (fun a : U => (q l) >>= fun b : V => h a b)) =
    fun l => (privCompose p q l) >>= (fun z => h z.1 z.2) := by
  ext l x
  simp [privCompose, privComposeAdaptive]

/--
A noise function for a differential privacy system
-/
class DPNoise (dps : DPSystem T) where
  /--
  A noise mechanism (eg. Laplace, Discrete Gaussian, etc)
  Paramaterized by a query, sensitivity, and a (rational) security paramater.
  -/
  noise : Query T ℤ → (sensitivity : ℕ+) → (num : ℕ+) → (den : ℕ+) → Mechanism T ℤ
  /--
  Relationship between arguments to noise and resulting privacy amount
  -/
  noise_priv : (num : ℕ+) → (den : ℕ+) → (priv : NNReal) -> Prop
  /--
  Adding noise to a query makes it private
  -/
  noise_prop {q : List T → ℤ} {Δ εn εd : ℕ+} {ε : NNReal} :
    noise_priv εn εd ε ->
    sensitivity q Δ →
    dps.prop (noise q Δ εn εd) ε


class DPPar (T : Type) extends (DPSystem T) where
  prop_par {m1 : Mechanism T U} {m2 : Mechanism T V} {ε₁ ε₂ ε : NNReal} :
    ε = max ε₁ ε₂ -> ∀f, prop m1 ε₁ -> prop m2 ε₂ -> prop (privParCompose m1 m2 f) ε

end SLang
