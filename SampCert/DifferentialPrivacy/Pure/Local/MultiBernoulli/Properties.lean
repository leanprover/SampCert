import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang
import Mathlib.Data.Set.Basic
import SampCert.DifferentialPrivacy.Pure.Local.ENNRealLemmasSuite
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.Normalization

namespace MultiBernoulli
open SLang
open ENNRealLemmas

/- Normalization of the bernoulli_mapper. -/
lemma bernoulli_mapper_sums_to_1 (s : SeedType): ∑' (b : Bool), bernoulli_mapper s b = 1 := by
  rw[bernoulli_mapper]
  exact SLang.BernoulliSample_normalizes s.n s.d s.h

/- Normalization for MultiBernoulli, which is proven using our normaliation lemma. -/
lemma MultiBernoulliSample_normalizes [LawfulMonad SLang] (seeds : List SeedType) :
  ∑' (b: List Bool), MultiBernoulliSample seeds b = 1 := by
  unfold MultiBernoulliSample
  apply norm_func_norm_on_list
  intro a
  rw [bernoulli_mapper_sums_to_1]


end MultiBernoulli
