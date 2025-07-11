import SampCert
open SLang

namespace MultiBernoulli

structure SeedType where
 /- This is just handy shorthand for a rational parameter n/d in [0, 1]-/
  n : Nat
  d : PNat
  h : n ≤ d

def bernoulli_mapper: SeedType -> SLang Bool :=
  fun s => SLang.BernoulliSample s.n s.d s.h

def MultiBernoulliSample (seeds: List SeedType): SLang (List Bool) :=
  seeds.mapM bernoulli_mapper

end MultiBernoulli
