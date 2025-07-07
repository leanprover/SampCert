import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert

namespace SLang

structure SeedType where
  n : Nat
  d : PNat
  h : n ≤ d

def MultiBernoulliSample (seeds: List SeedType): SLang (List Bool) :=
  seeds.mapM (fun s => SLang.BernoulliSample s.n s.d s.h)

#check @ENNReal.tsum_eq_iSup_sum
#check BernoulliSample_apply
#check BernoulliSample_normalizes

/- We'll need a proof that the MultiBernoulliSample applied to a single-element
   list is the same thing as the usual BernoulliSample -/

lemma MultiBernoulli_single_list (hd : SeedType): ∑' (b : List Bool), MultiBernoulliSample [hd] b = 1 := by
   rw [MultiBernoulliSample]
   rw [ENNReal.tsum_eq_add_tsum_ite]
   sorry


lemma MultiBernoulli_independence (hd : SeedType) (tl : List SeedType):
  ∑' (b : List Bool), MultiBernoulliSample (hd :: tl) b =
  (∑' (b : List Bool), MultiBernoulliSample [hd] b) * ∑' (b : List Bool), MultiBernoulliSample tl b := by
    sorry

lemma MultiBernoulliSample_normalizes (seeds : List SeedType) :
  HasSum (MultiBernoulliSample seeds) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    induction seeds with
    | nil => rw [MultiBernoulliSample]
             rw [@List.mapM_nil]
             simp[pure]
             rw [ENNReal.tsum_eq_add_tsum_ite []]
             simp_all only [↓reduceIte, ite_self, tsum_zero, add_zero]
    | cons hd tl ih =>
      rw [MultiBernoulli_independence hd tl]
      rw [ih]
      rw [@CanonicallyOrderedCommSemiring.mul_one]
      rw[MultiBernoulli_single_list]
