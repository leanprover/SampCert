import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang
import Mathlib.Data.Set.Basic
import SampCert.DifferentialPrivacy.Local.ENNRealLemmasSuite
import SampCert.DifferentialPrivacy.Local.MultiBernoulli.Code


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

lemma simplifier1 (a : List Bool) (b : Bool):
(∑' (a_1 : List Bool), if a = b :: a_1 then mapM bernoulli_mapper tl a_1 else 0) =
(if a.head? = b then mapM bernoulli_mapper tl a.tail else 0) := by
  cases a with
  | nil => simp
  | cons ah atl =>
    simp [-mapM]
    split
    next h =>
      subst h
      simp_all only [true_and]
      rw [tsum_eq_single]
      split
      rename_i h
      on_goal 2 => rename_i h
      apply Eq.refl
      simp_all only [not_true_eq_false]
      intro b' a
      simp_all only [ne_eq, mapM, ite_eq_right_iff]
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]
    next h => simp_all only [false_and, ↓reduceIte]
              simp [tsum_ite_not]

lemma list_bool_tsum_only_tl (b : Bool) (f : List Bool -> ENNReal):
∑' (a : List Bool), f a = ∑' (a : List Bool), if a.head? = some b then f a.tail else 0 := by
 apply Equiv.tsum_eq_tsum_of_support
 sorry

lemma simplifier2 (hd : SeedType) (tl : List SeedType) (b : Bool):
(∑' (a : List Bool), bernoulli_mapper hd b * if a.head? = some b then mapM bernoulli_mapper tl a.tail else 0) =
 ∑' (a : List Bool), bernoulli_mapper hd b * mapM bernoulli_mapper tl a := by
  simp_all only [mul_ite, mul_zero]
  apply symm
  apply list_bool_tsum_only_tl b

lemma simplifier3:
 ∑' (a : Bool), bernoulli_mapper hd a * mapM bernoulli_mapper tl b = mapM bernoulli_mapper tl b := by
  rw [tsum_bool]
  rw [ennreal_mul_assoc]
  rw [←tsum_bool]
  rw [bernoulli_mapper_sums_to_1]
  rw [@CanonicallyOrderedCommSemiring.one_mul]

lemma MultiBernoulliSample_normalizes [LawfulMonad SLang] (seeds : List SeedType) :
  ∑' (b: List Bool), MultiBernoulliSample seeds b = 1 := by
    rw [MultiBernoulliSample]
    induction seeds with
    | nil => rw [@List.mapM_nil]
             simp[pure]
             rw [ENNReal.tsum_eq_add_tsum_ite []]
             simp_all only [↓reduceIte, ite_self, tsum_ite_not, add_zero]
             simp
    | cons hd tl ih =>
      simp [List.mapM_cons, -mapM]
      conv =>
        enter [1, 1, b, 1, a]
        simp [-mapM]
        rw [simplifier1]
      /- rewrite as a double sum, the first sum being over possible a.heads, and the second
         some being over all list Bools, with the conditional now being on the Boolean
         in the first sum. Afterwards, it should be straightforward to use the inductive hypothesis -/
      rw [@ENNReal.tsum_comm]
      conv =>
        enter [1, 1, b]
        rw [simplifier2]
      rw [@ENNReal.tsum_comm]
      conv =>
        enter [1, 1, b]
        rw [simplifier3]
      apply ih

end MultiBernoulli
