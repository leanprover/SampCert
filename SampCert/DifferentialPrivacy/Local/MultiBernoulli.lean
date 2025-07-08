import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang

namespace MultiBernoulli

structure SeedType where
  n : Nat
  d : PNat
  h : n ≤ d

def bernoulli_mapper: SeedType -> SLang Bool :=
  fun s => SLang.BernoulliSample s.n s.d s.h

noncomputable def explicit_prob (hd : SeedType) (tl : List SeedType) (b : List Bool) : ENNReal :=
  match b with
    | [] => 0
    | x :: xs => bernoulli_mapper hd x * (mapM bernoulli_mapper tl) xs

def MultiBernoulliSample (seeds: List SeedType): SLang (List Bool) :=
  seeds.mapM bernoulli_mapper

#check MultiBernoulliSample [SeedType.mk 1 2 (by decide), SeedType.mk 1 2 (by decide)] [true, false]

#check @ENNReal.tsum_eq_iSup_sum
#check SLang.BernoulliSample_apply
#check SLang.BernoulliSample_normalizes
#check List.mapM_cons
#check SLang
#check List.mapM_nil
#check tsum_eq_single

/- We'll need a proof that the MultiBernoulliSample applied to a single-element
   list is the same thing as the usual BernoulliSample -/

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

lemma bernoulli_mapper_neq_iff (l : List SeedType) (b : List Bool) :
  mapM bernoulli_mapper l [] =
    match l with
    | [] => 1
    | hd :: tl => 0 := by
      cases l with
      | nil =>  simp[-mapM]
      | cons hd tl => simp[-mapM]
                      sorry

lemma multi_bernoulli_explicit (hd : SeedType) (tl : List SeedType) (b : List Bool):
  mapM bernoulli_mapper (hd :: tl) b = explicit_prob hd tl b := by
  unfold explicit_prob
  rw[List.mapM_cons]
  simp_all only [bind, pure, SLang.bind_apply, SLang.pure_apply, mul_ite, mul_one, mul_zero]
  split
  next b => simp_all only [↓reduceIte, tsum_zero, mul_zero]
  next b x xs =>
    simp_all only [List.cons.injEq]
    rw[tsum_bool]
    cases x with
    | false => simp[-mapM]
               rw[tsum_eq_single xs]
               simp_all
               intro b' a
               simp_all only [ne_eq, mapM, ite_eq_right_iff]
               intro a_1
               subst a_1
               simp_all only [not_true_eq_false]
    | true =>  simp[-mapM]
               rw[tsum_eq_single xs]
               simp_all
               intro b' a
               simp_all only [ne_eq, mapM, ite_eq_right_iff]
               intro a_1
               subst a_1
               simp_all only [not_true_eq_false]
  sorry

lemma multi_bernoulli_explicit_sum (hd : SeedType) (tl : List SeedType):
 ∑' (b : List Bool), mapM bernoulli_mapper (hd :: tl) b = ∑' (b : List Bool), explicit_prob hd tl b := by
  simp_all [multi_bernoulli_explicit, -mapM]

lemma MultiBernoulli_independence (hd : SeedType) (tl : List SeedType):
  ∑' (b : List Bool), MultiBernoulliSample (hd :: tl) b =
  (∑' (b : List Bool), MultiBernoulliSample [hd] b) * ∑' (b : List Bool), MultiBernoulliSample tl b := by
    sorry

lemma MultiBernoulliSample_normalizes (seeds : List SeedType) :
  ∑' (b: List Bool), MultiBernoulliSample seeds b = 1 := by
    induction seeds with
    | nil => rw [MultiBernoulliSample]
             rw [@List.mapM_nil]
             simp[pure]
             rw [ENNReal.tsum_eq_add_tsum_ite []]
             simp_all only [↓reduceIte, ite_self, tsum_zero, add_zero]
    | cons hd tl ih =>
      rw [MultiBernoulli_independence hd tl]
      rw [ih]
      rw[MultiBernoulli_single_list hd]
      rw [one_mul]


noncomputable def push_forward {T S: Type} [DecidableEq S] (p : SLang T) (f : T -> S) : SLang S :=
  fun s => ∑' (t : T), if f t = s then p t else 0

lemma push_forward_prob_is_prob {T S : Type} [DecidableEq S] (p : SLang T) (f : T -> S) (h : ∑' (t : T), p t = 1) :
  ∑' (s : S), (push_forward p f) s = 1 := by
    simp [push_forward]
    rw [@ENNReal.tsum_comm]
    have h1: ∀b : T, ∑' (a : S), (if f b = a then p b else 0 : ENNReal) = p b := by
      intro b
      rw [tsum_eq_single (f b)]
      simp
      intro b' a
      simp_all only [ne_eq, ite_eq_right_iff]
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]
    simp_all

end MultiBernoulli
