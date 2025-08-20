import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.Postprocessing
import SampCert.DifferentialPrivacy.Generic

namespace SLang

-- Implementation of the Shuffler for the Shuffle Model.
def Shuffler {α: Type}(l:List α) := do
match l with
| [] => pure []
| hd::tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd

/- This is the  implementation of the Shuffle algorithm using Randomized Response as the local randomizer.  -/
def RRShuffle(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ← Shuffler l
  return b

/- Definition of a function that uniformly permutes a given list.-/
def UniformShuffler {U: Type}[BEq U](f: List U → SLang (List U)) : Prop :=
  ∀ l₁ l₂: List U, f l₁ l₂ = if List.isPerm l₁ l₂ then (1: ENNReal)/(l₁.length.factorial) else (0: ENNReal)

/- Generalized version of the shuffle algorithm that takes in any mechanism -/
def ShuffleAlgorithm [BEq U](m : Mechanism T  (List U))(f : List U → SLang (List U))(_: UniformShuffler f)(l: List T) := do
  let x ← (m l).toSLang
  let b ← f x
  return b

noncomputable def num_perms (l : List U) [BEq U] [DecidableEq (List U)] : ENNReal := ((List.permutations l).toFinset).card

def UniformShuffler_v2 {U : Type} [BEq U] [DecidableEq (List U)] (f : List U → SLang (List U)) : Prop :=
 ∀ l : List U, ∀ a : List U, (List.isPerm l a → f l a = (num_perms a)⁻¹) ∧ (¬ List.isPerm l a → f l a = 0)

lemma UniformShuffler_v2_norms {U : Type} [BEq U] [DecidableEq U] [DecidableEq (List U)] (f : List U → SLang (List U)) (h : UniformShuffler_v2 f) (l : List U): HasSum (f l) 1 := by
  simp [Summable.hasSum_iff]
  have h1 (b : List U): f l b = (if List.isPerm l b then (num_perms l)⁻¹ else 0) := by
    cases h_perm: (l.isPerm b == true) with
    | true =>
      simp at h_perm
      simp [UniformShuffler_v2] at h
      induction l generalizing b with
      | nil =>
        simp_all [List.isPerm, List.isEmpty]
        aesop
      | cons hd tl ih =>
        cases hb : (hd :: tl).isPerm b with
        | true => simp
                  sorry
        | false => simp [hb]
                   apply (h (hd :: tl) b).right hb
    | false =>
      simp at h_perm
      simp_all only [Bool.false_eq_true, ↓reduceIte, CharP.cast_eq_zero]
      simp [UniformShuffler_v2] at h
      apply (h l b).right h_perm
  conv =>
    enter [1, 1, b]
    rw [h1]
  have h2: ∑' (b : List U), (if l.isPerm b then ((num_perms l)⁻¹) else 0) = (num_perms l) * (num_perms l)⁻¹ := by
    sorry
  rw [h2]
  apply ENNReal.mul_inv_cancel
  simp [num_perms, List.permutations]
  simp [num_perms, List.permutations]
