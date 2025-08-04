import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code

namespace SLang





def single_swap {T:Type}(l:Array T)(i: PNat)(h: i < l.size) := do
  let j ← UniformSample i
  return l.swap ⟨i.val, h⟩ ⟨j, sorry⟩




def Shuffler {α: Type}(l:List α): SLang (List α) :=
  let a := l.toArray
  sorry


def reverseIterSafe {α : Type} (a : Array α) : Array α :=
  Array.range a.size |>.reverse |>.map (λ i => a.get! i)
