import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import SampCert
import SampCert.SLang
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import SampCert.DifferentialPrivacy.Pure.Local.ENNRealLemmasSuite

/- In this file, we show that if a function f : α -> SLang β
   normalizes, in the sense that ∑' (b : List β) f a b = 1
   for any fixed a : α,
   then the function obtained by applying monadic map
   to f and some list also normalizes.
   This is valuable for local algorithms, where
   a randomizer is first defined for a single user and then
   applied to a dataset of users.
-/

/- Helper lemma to simplify a if-then-else statement in a sum-/
lemma simplifier1_gen (α β : Type) [DecidableEq β](f: α → SLang β) (a : List β) (b : β)(tl : List α):
(∑' (a_1 : List β), if a = b :: a_1 then mapM f tl a_1 else 0) =
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

open Set

/- This lemma shows that summing a function over all possible lists is the same as summing a function
   over all tails of lists with a specified head.
-/
lemma list_beta_tsum_only_tl (β : Type) [DecidableEq β] (b : β) (f : List β -> ENNReal):
∑' (a : List β), f a = ∑' (a : List β), if a.head? = some b then f a.tail else 0 := by
  apply Equiv.tsum_eq_tsum_of_support
  intro x
  case e =>
    let e₁ := Equiv.Set.image (List.cons b) (Function.support f) (fun _ _ h => List.cons_injective h)
    have h_eq : (List.cons b) '' (Function.support f) =
        Function.support (fun y => if y.head? = some b then f y.tail else 0) := by
      rw [@Set.ext_iff]
      intro L
      apply Iff.intro
      { intro hx
        have lhead: L.head? = some b := by
          simp_all only [mem_image, Function.mem_support, ne_eq]
          obtain ⟨w, h⟩ := hx
          obtain ⟨_, right⟩ := h
          subst right
          simp_all only [List.head?_cons]
        rw[Function.support]
        rw [@mem_setOf]
        rw [lhead]
        simp
        simp_all only [mem_image, Function.mem_support, ne_eq]
        obtain ⟨w, h⟩ := hx
        obtain ⟨left, right⟩ := h
        subst right
        simp_all only [List.head?_cons, List.tail_cons, not_false_eq_true]
      }
      { intro hx
        rw [Function.support] at hx
        rw [@mem_setOf] at hx
        have lhead: L.head? = some b := by simp_all only [ne_eq, ite_eq_right_iff, Classical.not_imp]
        simp_all only [↓reduceIte, ne_eq, mem_image, Function.mem_support]
        apply Exists.intro L.tail
        apply And.intro
        exact hx
        rw [List.cons_head?_tail lhead]
      }
    let e₂ := Equiv.Set.ofEq h_eq
    exact e₁.trans e₂
  case he => simp

/- Another simplifying lemma for if-then-else statements within a sum.-/
lemma simplifier2_gen (α β : Type) [DecidableEq β] (f: α → SLang β)(hd : α) (tl : List α) (b : β):
(∑' (a : List β), f hd b * if a.head? = some b then mapM f tl a.tail else 0) =
 ∑' (a : List β), f hd b * mapM f tl a := by
  simp_all only [mul_ite, mul_zero]
  apply symm
  apply list_beta_tsum_only_tl β b

/- Simplifying lemma to pull a constant out of a sum. -/
lemma simplifier3_gen [LawfulMonad SLang] (α β : Type)(f : α → SLang β)(hd : α)(tl : List α) (b : List β) (h : ∑' (b : β), f hd b = 1): ∑' (a : β), f hd a * mapM f tl b = mapM f tl b := by
  have : ∑' (a : β), f hd a * mapM f tl b = (∑' (a : β), f hd a) * mapM f tl b := by
    rw [ENNReal.tsum_mul_right]
  rw [this, h, one_mul]

/- The key normalization lemma, which shows that if a function f
   normalizes, then the function obtained applying monadic map to f and some list al
   also normalizes.
-/
lemma Norm_func_norm_on_list [LawfulMonad SLang] (α β : Type) [DecidableEq β] (f: α → SLang β) (al: List α):
 (∀ a : α, ∑' (b : β), f a b = 1) →  ∑' (b : List β), mapM f al b = 1 := by
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
