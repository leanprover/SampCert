import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Basic

namespace SLang

/- Implementation of the Shuffler for the Shuffle Model.
   Outputs a random permutation of the input list. -/
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

def num_perms {α: Type} (l: List α) [DecidableEq α]: ℕ := (l.permutations.toFinset).card

/- Definition of a function that uniformly permutes a given list.-/
def UniformShuffler {U: Type}[BEq U] [DecidableEq U] (f: List U → SLang (List U)) : Prop :=
  ∀ l₁ l₂: List U, f l₁ l₂ = if List.isPerm l₁ l₂ then (1: ENNReal)/(num_perms l₁) else (0: ENNReal)

/- Generalized version of the shuffle algorithm that takes in any mechanism -/
def ShuffleAlgorithm [BEq U][DecidableEq U] (m : Mechanism T  (List U))(f : List U → SLang (List U))(_: UniformShuffler f)(l: List T) := do
  let x ← (m l).toSLang
  let b ← f x
  return b
