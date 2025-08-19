import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
namespace SLang

def my_func {α: Type} (l:Array α) := do
let mut l := l
for h: i in [1:l.size] do
  let j ← UniformSample (Nat.toPNat' i: PNat)
  l := l.swap ⟨i, sorry⟩ ⟨j, sorry⟩
return l

#check my_func

def Shuffler {α: Type}(l:List α) := do
let mut a := l.toArray
for h: i in [1:a.size] do
  let j ← UniformSample (Nat.toPNat' i: PNat)
  a := a.swap ⟨i, sorry⟩ ⟨j, sorry⟩
return a

#check my_func
#check Array.swap
