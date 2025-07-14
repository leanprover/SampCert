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

lemma bernoulli_mapper_sums_to_1 (s : SeedType): ∑' (b : Bool), bernoulli_mapper s b = 1 := by
  rw[bernoulli_mapper]
  exact SLang.BernoulliSample_normalizes s.n s.d s.h

lemma bernoulli_mapper_empty (b : List Bool): mapM bernoulli_mapper [] b = if b = [] then 1 else 0 := by
  rw [@List.mapM_nil]
  simp_all only [pure, SLang.pure_apply, ite_eq_right_iff, one_ne_zero, imp_false]
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only

/- The following theorems might be useful, but are not used in the current proof -/

lemma MultiBernoulli_single_list [LawfulMonad SLang] (hd : SeedType): ∑' (b : List Bool), MultiBernoulliSample [hd] b = 1 := by
  rw [MultiBernoulliSample]
  rw [List.mapM_cons, List.mapM_nil]
  rcases hd with ⟨n, d, h⟩
  simp only [pure, bind]
  simp_all only [SLang.pure_bind, SLang.bind_apply, SLang.pure_apply, mul_ite, mul_one, mul_zero]
  rw [@ENNReal.tsum_comm]
  rw [tsum_bool]
  simp_all only [Bool.false_eq_true, ↓reduceIte, tsum_ite_eq]
  rw[←tsum_bool]
  rw[bernoulli_mapper]
  rw [SLang.BernoulliSample_normalizes]

lemma bernoulli_helper [LawfulMonad SLang] (hd : Bool) (hd_1 : SeedType) : bernoulli_mapper hd_1 hd = mapM bernoulli_mapper [hd_1] [hd] := by
  rw [List.mapM_cons, List.mapM_nil]
  rcases hd_1 with ⟨n, d, h⟩
  simp only [pure, bind]
  simp_all only [SLang.pure_bind, SLang.bind_apply, SLang.pure_apply, mul_ite, mul_one, mul_zero]
  simp_all only [List.cons.injEq, and_true]
  cases hd with
  | true => simp_all only [Bool.true_eq, tsum_ite_eq]
  | false => simp_all only [Bool.false_eq, tsum_ite_eq, tsum_ite_not, mul_zero]

lemma MultiBernoulliSample_normalizes [LawfulMonad SLang] (seeds : List SeedType) :
  ∑' (b: List Bool), MultiBernoulliSample seeds b = 1 := by
  unfold MultiBernoulliSample
  apply Norm_func_norm_on_list
  intro a
  rw [bernoulli_mapper_sums_to_1]


end MultiBernoulli
