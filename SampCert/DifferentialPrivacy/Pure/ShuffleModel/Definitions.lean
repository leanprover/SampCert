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
