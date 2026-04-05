import SampCert
open SLang

namespace MultiBernoulli

/- We define the "MultiBernoulli" distribution to be the distribution associated with
   flipping each entry of a list with the same probability.-/

structure SeedType where
 /- This is just handy shorthand for a rational parameter n/d in [0, 1]-/
  n : Nat
  d : PNat
  h : n ≤ d

/- Obtains a Bernoulli sample taken from the seed.-/
def bernoulli_mapper: SeedType -> SLang Bool :=
  fun s => SLang.BernoulliSample s.n s.d s.h

/- Obtains a sample from the "MultiBernoulli" distribution. -/
def MultiBernoulliSample (seeds: List SeedType): SLang (List Bool) :=
  seeds.mapM (fun s => bernoulli_mapper s)

end MultiBernoulli
