import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code

namespace SLang


def swapAt {α : Type} (arr : Array α) (i j : Nat) : Array α :=
  if h1 : i < arr.size ∧ j < arr.size then
    let tmp := arr[i]
    arr.set! i arr[j] |>.set! j tmp
  else
    arr


def single_swap {T:Type}(l: Array T)(i: PNat) := do
  let j ← UniformSample i
  return l.swap ⟨i, sorry⟩ ⟨j, sorry⟩

#check single_swap


def Shuffler {α: Type}(l:List α) := do
  let mut a := l.toArray
  for h: i in [1:a.size] do
   let j ← UniformSample (Nat.toPNat' i)
   a := a.swap ⟨i, sorry⟩ ⟨j, sorry⟩
  return a
