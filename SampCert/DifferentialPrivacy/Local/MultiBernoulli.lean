import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang

namespace MultiBernoulli

structure SeedType where
  n : Nat
  d : PNat
  h : n ≤ d

def mapper_funct: SeedType -> SLang Bool :=
  fun s => SLang.BernoulliSample s.n s.d s.h

noncomputable def explicit_sample (hd : SeedType) (tl : List SeedType) (b : List Bool) : ENNReal :=
  match b with
    | [] => 0
    | x :: xs => mapper_funct hd x * (mapM mapper_funct tl) xs

def MultiBernoulliSample (seeds: List SeedType): SLang (List Bool) :=
  seeds.mapM mapper_funct

#check MultiBernoulliSample [SeedType.mk 1 2 (by decide), SeedType.mk 1 2 (by decide)] [true, false]

#check @ENNReal.tsum_eq_iSup_sum
#check SLang.BernoulliSample_apply
#check SLang.BernoulliSample_normalizes
#check List.mapM_cons
#check SLang

#check List.mapM_cons
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
  rw[mapper_funct]
  rw [SLang.BernoulliSample_normalizes]

lemma mapper_funct_neq_iff (l : List SeedType) (b : List Bool) :
  mapM mapper_funct l [] =
    match l with
    | [] => 1
    | _ => 0 := by
      cases l with
      | nil =>  simp[-mapM]
      | cons hd tl => simp[-mapM]
                      sorry


lemma MultiBernoulliSampler_recurrence (hd : SeedType) (tl : List SeedType) (b : List Bool):
  mapM mapper_funct (hd :: tl) b
= explicit_sample hd tl b := by
  unfold explicit_sample
  rw[List.mapM_cons]
  aesop
  sorry

lemma test_2 (hd : SeedType) (tl : List SeedType):
 ∑' (b : List Bool), mapM mapper_funct (hd :: tl) b = ∑' (b : List Bool), explicit_sample hd tl b := by
  sorry

lemma MultiBernoulli_independence (hd : SeedType) (tl : List SeedType):
  ∑' (b : List Bool), MultiBernoulliSample (hd :: tl) b =
  (∑' (b : List Bool), MultiBernoulliSample [hd] b) * ∑' (b : List Bool), MultiBernoulliSample tl b := by
    rw [MultiBernoulliSample]
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
      sorry
    simp_all

end MultiBernoulli
