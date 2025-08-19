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

def Shuffler {α: Type}(l:List α) := do
match l with
| [] => pure []
| hd::tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd

  /- This is the Shuffle Model. -/
def RRShuffle(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ← Shuffler l
  return b

#check Shuffler
#check RandomizedResponse.RRSample
#check Mechanism

def UniformShuffler {U: Type}[BEq U](f: List U → SLang (List U)) : Prop :=
  ∀ l₁ l₂: List U, f l₁ l₂ = if List.isPerm l₁ l₂ then (1: ENNReal)/(l₁.length.factorial) else (0: ENNReal)


def ShuffleAlgorithm [BEq U](m : List T → SLang (List U))(f : List U → SLang (List U))(_: UniformShuffler f)(l: List T) := do
  let x ← m l
  let b ← f x
  return b

def BinomialSample (seed: MultiBernoulli.SeedType)(n:PNat) := do
  let seeds := List.replicate n seed
  let list ← MultiBernoulli.MultiBernoulliSample (seeds)
  let k := List.count true list
  return k
