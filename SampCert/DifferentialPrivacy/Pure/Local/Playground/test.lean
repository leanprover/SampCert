
import Mathlib.Data.ENNReal.Basic



lemma valid_index2 {l₁ : List T} (h1: l₁ = a++[n]++b) (i : Fin ((l₁.length - 1) + 1)):
  i.val < l₁.length := by
    have hl1: l₁.length - 1 + 1 = l₁.length := by
      rw [Nat.sub_add_cancel]
      rw[h1]
      simp
      linarith
    exact Nat.lt_of_lt_of_eq i.2 hl1

lemma conversion2 (l: List T) (x: List Bool)(h1: l = a++[n]++b)(hx: l.length = x.length)(f: T → Bool → ENNReal): (∏' (i : Fin (l.length)), f (l[i.val]'(by simp)) (x[i.val]'(by rw[← hx];simp))) = (∏' (i : Fin ((l.length-1)+1)), f (l[i.val]'(by sorry)) (x[i.val]'(by rw[← hx];sorry))) := by
  rw[Nat.sub_add_cancel]
  rw[h1]
  simp
  linarith

lemma conversion (l: List T) (x: List Bool)(h1: l = a++[n]++b)(hx: l.length = x.length)(f: T → Bool → ENNReal): (∏' (i : Fin (l.length)), f (l[i.val]'(by simp)) (x[i.val]'(by rw[← hx];simp))) = (∏' (i : Fin ((l.length-1)+1)), f (l[i.val]'(valid_index2 h1 i)) (x[i.val]'(by rw[← hx];sorry))) := by
  rw[Nat.sub_add_cancel]
  rw[h1]
  simp
  linarith
