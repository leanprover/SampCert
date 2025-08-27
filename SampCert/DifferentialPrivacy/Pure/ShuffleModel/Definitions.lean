import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Basic

namespace SLang
open Classical

/- Implementation of the Shuffler for the Shuffle Model.
   Outputs a random permutation of the input list.
   This is a bit unsatisfactory,
   since we have not actually shown that the output distribution is uniform. -/
def Shuffler {α: Type}(l:List α): SLang (List α) := do
match l with
| [] => return []
| hd :: tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd

/- This is the  implementation of the Shuffle algorithm using randomized response as the local randomizer.  -/
def RRShuffle(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ← Shuffler l
  return b

/- Computes the number of permutations of a list, accounting
   for the number of unique elements in the list. -/

def num_perms {α: Type} [DecidableEq α] (l: List α): ℕ := (l.permutations.toFinset).card

/- Definition of a function that produces random permutations. -/
def UniformShuffler {U: Type} (f: List U → SLang (List U)) : Prop :=
  ∀ l₁ l₂: List U, f l₁ l₂ = if List.isPerm l₁ l₂ then (num_perms l₁ : ENNReal)⁻¹ else (0: ENNReal)

/- Generalized version of the shuffle algorithm that takes in any mechanism. -/
def ShuffleAlgorithm (m : Mechanism T (List U))(f : List U → SLang (List U))(_: UniformShuffler f)(l: List T) := do
  let x ← (m l).toSLang
  let b ← f x
  return b
