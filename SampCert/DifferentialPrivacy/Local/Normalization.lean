import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang
import Mathlib.Data.Set.Basic

lemma simplifier1_gen (α : Type)(f: α → SLang Bool) (a : List Bool) (b : Bool)(tl : List α):
(∑' (a_1 : List Bool), if a = b :: a_1 then mapM f tl a_1 else 0) =
(if a.head? = b then mapM f tl a.tail else 0) := by
  cases a with
  | nil => simp
  | cons ah atl =>
    simp [-mapM]
    split
    next h =>
      subst h
      simp_all only [true_and]
      rw [tsum_eq_single]
      --simp_all only [mapM]
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
    next h => simp_all only [false_and, ↓reduceIte, _root_.tsum_zero]

lemma simplifier2_gen (α : Type)(f: α → SLang Bool)(hd : α) (tl : List α) (b : Bool):
(∑' (a : List Bool), f hd b * if a.head? = some b then mapM f tl a.tail else 0) =
 ∑' (a : List Bool), f hd b * mapM f tl a := by
  simp_all only [mul_ite, mul_zero]
  apply symm
  sorry

lemma ennreal_mul_assoc (a b c : ENNReal): a * c + b * c = (a + b) * c := by ring

lemma simp_4 [LawfulMonad SLang] (α : Type)(a : α)(f: α → SLang Bool): ∑' (i : Bool), f a i = ∑' (b : Bool), f a b := by
  rfl

lemma simplifier3_gen [LawfulMonad SLang] (α : Type)(f : α → SLang Bool)(hd : α)(tl : List α) (h : ∑' (b : Bool), f hd b = 1): ∑' (a : Bool), f hd a * mapM f tl b = mapM f tl b := by
  rw [tsum_bool]
  rw [ennreal_mul_assoc]
  rw [←tsum_bool]
  rw [simp_4]
  rw [h]
  rw [@CanonicallyOrderedCommSemiring.one_mul]



lemma Norm_func_norm_on_list [LawfulMonad SLang] (α : Type)(f: α → SLang Bool) (al: List α):
 (∀ a : α, ∑' (b : Bool), f a b = 1) →  ∑' (b : List Bool), mapM f al b = 1 := by
  intro h
  induction al with
  | nil =>
    rw [@List.mapM_nil]
    simp[pure]
    rw [ENNReal.tsum_eq_add_tsum_ite []]
    simp_all only [↓reduceIte, ite_self, tsum_zero, add_zero]
  | cons hd tl ih =>
    simp [List.mapM_cons, -mapM]
    conv =>
      enter [1, 1, b, 1, a]
      simp [-mapM]
      rw [simplifier1_gen]
      /- rewrite as a double sum, the first sum being over possible a.heads, and the second
         some being over all list Bools, with the conditional now being on the Boolean
         in the first sum. Afterwards, it should be straightforward to use the inductive hypothesis -/
    rw [@ENNReal.tsum_comm]
    conv =>
      enter [1, 1, b]
      rw [simplifier2_gen]
    rw [@ENNReal.tsum_comm]
    conv =>
      enter [1, 1, b]
      rw [simplifier3_gen]
      rfl
      rw[h hd]
    apply ih
