import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code

namespace SLang

def swap{T: Type}(l: Array T)(i j : Nat)(hi: i <l.size)(hj: j < l.size): List T :=
  l.swap


def single_swap {T:Type}(i: PNat)(l:List T)(h: i <  l.length) := do
  let j ← UniformSample i





def Shuffler {T: Type}(l: List T): List T :=
  let r ←
