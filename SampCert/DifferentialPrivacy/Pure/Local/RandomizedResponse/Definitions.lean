import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
/-import SampCert.DifferentialPrivacy.Local.MultiBernoulli -/

open SLang
/- open MultiBernoulli -/

lemma arith_0 (num : Nat) (den : PNat) (_ : 2 * num ≤ den): den - 2*num ≤ 2 * den := by
  simp_all only [tsub_le_iff_right]
  linarith

def RRSingleSample  {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
  let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
  return Bool.xor (query l) r

def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample2 on an entire dataset. -/
 l.mapM (fun x => RRSingleSample query num den h x)

 /- def RRSample2 {T : Type} (query : T -> Bool) (seed_list : List SeedType) (l : List T): SLang (List Bool) := do
  let r ← MultiBernoulliSample seed_list
  return List.zipWith (fun u s => Bool.xor (query u) s) l r -/

/- At this point, we should be set to prove that RRSample is normalized and that it is
   differentially private. The definition is computable, as we need. -/
