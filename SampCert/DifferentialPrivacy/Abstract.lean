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
-/

noncomputable section

open Classical Nat Int Real ENNReal

def NonZeroNQ (nq : List T → PMF U) :=
  ∀ l : List T, ∀ n : U, nq l n ≠ 0

def NonTopSum (nq : List T → PMF U) :=
  ∀ l : List T, ∑' n : U, nq l n ≠ ⊤

-- -- FIXME: Remove
-- def NormalMechanism (q : List T -> PMF U) : Prop :=
--   ∀ l, HasSum (q l) 1

namespace SLang

abbrev Query (T U : Type) := List T → U
abbrev Mechanism (T U : Type) := List T → PMF U

-- instance : Coe (Mechanism T U) (List T -> SLang U) where
--   coe m l := m l

/--
Product of mechanisms.
-/
def privCompose (nq1 : Mechanism T U) (nq2 : Mechanism T V) (l : List T) : PMF (U × V) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

/--
Mechanism obtained by applying a post-processing function to a mechanism.
-/
def privPostProcess (nq : Mechanism T U) (pp : U → V) (l : List T) : PMF V := do
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
  Predicate which must hold on a function for postcompostion
  -/
  postprocess_prop_f : {U V : Type} -> (f : U -> V) -> Prop
  /--
  Notion of privacy is invariant under post-processing.
  -/
  postprocess_prop : {U : Type} → [MeasurableSpace U] → [Countable U] → [DiscreteMeasurableSpace U] → [Inhabited U] → { pp : U → V } → postprocess_prop_f pp → ∀ m : Mechanism T U, ∀ ε₁ ε₂ : ℕ+,
   prop m (ε₁ / ε₂) → prop (privPostProcess m pp) (ε₁ / ε₂)

@[simp]
lemma bind_bind_indep (p : Mechanism T U) (q : Mechanism T V) (h : U → V → PMF A)  :
  (fun l => (p l) >>= (fun a : U => (q l) >>= fun b : V => h a b))
    =
  fun l => (privCompose p q l) >>= (fun z => h z.1 z.2) := by
  ext l x
  simp [privCompose, tsum_prod']
  -- apply tsum_congr
  -- intro b
  -- rw [← ENNReal.tsum_mul_left]
  -- apply tsum_congr
  -- intro c
  -- rw [← mul_assoc]
  -- congr 1
  -- rw [tsum_eq_single b]
  -- . congr 1
  --   rw [tsum_eq_single c]
  --   . simp
  --   . intro b' h1
  --     simp
  --     intro h2
  --     subst h2
  --     contradiction
  -- . intro b' h1
  --   rw [tsum_eq_single c]
  --   . simp
  --     intro h2
  --     subst h2
  --     contradiction
  --   . intro b'' h2
  --     simp
  --     intro h3 h4
  --     subst h3
  --     subst h4
  --     contradiction

lemma compose_sum_rw (nq1 : U -> ENNReal) (nq2 : V -> ENNReal) (b : U) (c : V) :
  (∑' (a : U), nq1 a * ∑' (a_1 : V), if b = a ∧ c = a_1 then nq2 a_1 else 0) = nq1 b * nq2 c := by
  have A : ∀ a : U, ∀ b : U, (∑' (a_1 : V), if b = a ∧ c = a_1 then nq2 a_1 else 0) = if b = a then (∑' (a_1 : V), if c = a_1 then nq2 a_1 else 0) else 0 := by
    intro x  y
    split
    . rename_i h
      subst h
      simp
    . rename_i h
      simp
      intro h
      contradiction
  conv =>
    left
    right
    intro a
    right
    rw [A]
  rw [ENNReal.tsum_eq_add_tsum_ite b]
  simp
  have B : ∀ x : U, (if x = b then 0 else if b = x then nq1 x * ∑' (a_1 : V), if c = a_1 then nq2 a_1 else 0 else 0) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [B]
  simp
  congr 1
  rw [ENNReal.tsum_eq_add_tsum_ite c]
  simp
  have C :∀ x : V,  (if x = c then 0 else if c = x then nq2 x else 0) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro X
    rw [C]
  simp

-- Unused
/-
Composed queries are normalizable.
-/
-- theorem privCompose_NonTopSum {nq1 : Mechanism T U} {nq2 : Mechanism T V} (nt1 : NonTopSum nq1) (nt2 : NonTopSum nq2) :
--   NonTopSum (privCompose nq1 nq2) := by
--   simp [NonTopSum] at *
--   intro l
--   replace nt1 := nt1 l
--   replace nt2 := nt2 l
--   simp [privCompose]
--   rw [ENNReal.tsum_prod']
--   conv =>
--     right
--     left
--     right
--     intro a
--     right
--     intro b
--     simp
--     rw [compose_sum_rw]
--   conv =>
--     right
--     left
--     right
--     intro a
--     rw [ENNReal.tsum_mul_left]
--   rw [ENNReal.tsum_mul_right]
--   rw [mul_eq_top]
--   intro H
--   cases H
--   . rename_i H
--     cases H
--     contradiction
--   . rename_i H
--     cases H
--     contradiction

/--
All outputs of a composed query have nonzero probability.
-/
theorem privCompose_NonZeroNQ {nq1 : Mechanism T U} {nq2 : Mechanism T V} (nn1 : NonZeroNQ nq1) (nn2 : NonZeroNQ nq2) :
  NonZeroNQ (privCompose nq1 nq2) := by
  simp [NonZeroNQ] at *
  intro l a b
  replace nn1 := nn1 l a
  replace nn2 := nn2 l b
  simp [privCompose]
  exists a

theorem ENNReal.HasSum_fiberwise {f : T → ENNReal} {a : ENNReal} (hf : HasSum f a) (g : T → V) :
    HasSum (fun c : V ↦ ∑' b : g ⁻¹' {c}, f b) a := by
  let A := (Equiv.sigmaFiberEquiv g)
  have B := @Equiv.hasSum_iff ENNReal T ((y : V) × { x // g x = y }) _ _ f a A
  replace B := B.2 hf
  have C := @HasSum.sigma ENNReal V _ _ _ _ (fun y : V => { x // g x = y }) (f ∘ ⇑(Equiv.sigmaFiberEquiv g)) (fun c => ∑' (b : ↑(g ⁻¹' {c})), f ↑b) a B
  apply C
  intro b
  have F := @Summable.hasSum_iff ENNReal _ _ _ (fun c => (f ∘ ⇑(Equiv.sigmaFiberEquiv g)) { fst := b, snd := c }) ((fun c => ∑' (b : ↑(g ⁻¹' {c})), f ↑b) b) _
  apply (F _).2
  . rfl
  . apply ENNReal.summable

theorem ENNReal.tsum_fiberwise (p : T → ENNReal) (f : T → V) :
  ∑' (x : V), ∑' (b : (f ⁻¹' {x})), p b
    = ∑' i : T, p i := by
  apply HasSum.tsum_eq
  apply ENNReal.HasSum_fiberwise
  apply Summable.hasSum
  exact ENNReal.summable

theorem fiberwisation (p : T → ENNReal) (f : T → V) :
 (∑' i : T, p i)
    = ∑' (x : V), if {a : T | x = f a} = {} then 0 else ∑'(i : {a : T | x = f a}), p i := by
  rw [← ENNReal.tsum_fiberwise p f]
  have A : ∀ x, f ⁻¹' {x} = { a | x = f a } := by
    intro x
    simp [Set.preimage]
    rw [Set.ext_iff]
    simp
    intro y
    exact eq_comm
  conv =>
    left
    right
    intro x
    rw [A]
  clear A
  apply tsum_congr
  intro b
  split
  . rename_i h'
    rw [h']
    simp only [tsum_empty]
  . simp

lemma condition_to_subset (f : U → V) (g : U → ENNReal) (x : V) :
  (∑' a : U, if x = f a then g a else 0) = ∑' a : { a | x = f a }, g a := by
  have A := @tsum_split_ite U (fun a : U => x = f a) g (fun _ => 0)
  simp only [decide_eq_true_eq, tsum_zero, add_zero] at A
  rw [A]
  have B : ↑{i | decide (x = f i) = true} = ↑{a | x = f a} := by
    simp
  rw [B]

theorem privPostProcess_NonZeroNQ {nq : Mechanism T U} {f : U → V} (nn : NonZeroNQ nq) (sur : Function.Surjective f) :
  NonZeroNQ (privPostProcess nq f) := by
  simp [NonZeroNQ, Function.Surjective, privPostProcess] at *
  intros l n
  replace sur := sur n
  cases sur
  rename_i a h
  exists a
  constructor
  . rw [h]
  . apply nn

-- theorem privPostProcess_NonTopSum {nq : Mechanism T U} (f : U → V) (nt : NonTopSum nq) :
--   NonTopSum (privPostProcess nq f) := by
--   simp [NonTopSum, privPostProcess] at *
--   intros l
--   have nt := nt l
--   rw [← ENNReal.tsum_fiberwise _ f] at nt
--   conv =>
--     right
--     left
--     right
--     intro n
--     rw [condition_to_subset]
--   have A : ∀ x : V, f ⁻¹' {x} = {y | x = f y} := by
--     aesop
--   conv =>
--     right
--     left
--     right
--     intro x
--     rw [← A]
--   trivial

-- lemma privCompose_norm (nq1 : List T → PMF U) (nq2 : List T → PMF V) (HNorm1 : NormalMechanism nq1) (HNorm2 : NormalMechanism nq2) : NormalMechanism (privCompose nq1 nq2) := by
--   rw [NormalMechanism] at *
--   intro l
--   have HNorm1' := HasSum.tsum_eq (HNorm1 l)
--   have HNorm2' := HasSum.tsum_eq (HNorm2 l)
--   have HR : (∑' (x : U × V), privCompose nq1 nq2 l x = 1) := by
--     rw [privCompose]
--     rw [ENNReal.tsum_prod']
--     simp
--     conv =>
--       lhs
--       arg 1
--       intro a
--       arg 1
--       intro b
--       rw [compose_sum_rw nq1 (fun l a_1 => nq2 l a_1) a b l]
--     conv =>
--       lhs
--       arg 1
--       intro a
--       rw [ENNReal.tsum_mul_left]
--     rw [ENNReal.tsum_mul_right]
--     rw [HNorm1']
--     rw [HNorm2']
--     simp
--   rw [<- HR]
--   apply Summable.hasSum
--   exact ENNReal.summable
--
-- lemma privPostProcess_norm (nq : List T → SLang U) (HNorm : NormalMechanism nq) (f : U -> V) : NormalMechanism (privPostProcess nq f) := by
--   rw [NormalMechanism] at *
--   intro l
--   have HR : (∑' (b : V), privPostProcess nq f l b = 1) := by
--     rw [privPostProcess]
--     simp
--     rw [<- HasSum.tsum_eq (ENNReal.HasSum_fiberwise (HNorm l) f)]
--     apply tsum_congr
--     intro v
--     rw [condition_to_subset]
--     have Htyeq : ({a | v = f a}) = (f ⁻¹' {v}) := by
--       rw [Set.ext_iff]
--       intro x
--       simp
--       exact eq_comm
--     rw [Htyeq]
--   rw [<- HR]
--   apply Summable.hasSum
--   exact ENNReal.summable
--
-- end SLang
