import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.RandomizedResponseMain

open RandomizedResponse


lemma fin_prod_cast_RAP {n m : ℕ} (h : n = m)(f : Fin n → ENNReal) :
  ∏' i : Fin n, f i = ∏' i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  simp

lemma conversion_RAP {β: Type}(l: List T) (x: List β)(h1: l = a++[n]++b)(hl : l.length ≥ 1)(hx: l.length = x.length)(f: T → SLang β): (∏' (i : Fin (l.length)), f (l[i.val]'(by simp)) (x[i.val]'(by rw[← hx];simp))) = (∏' (i : Fin ((l.length-1)+1)), f (l[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) := by
  rw [fin_prod_cast (by rw [← Nat.sub_add_cancel hl])]
  simp

lemma reduction2_RAP (n : Nat) (l₁ l₂: List T)(x: List (List Bool)) (f: Nat -> T → SLang (List Bool))(h1: l₁ = a++[l]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length) (hx2 : ∀ i : Fin (l₂.length - 1 + 1), (x[i]'(by sorry)).length = n) (hy: l₂.length = x.length) (nonzero: ∀(k: T) (bo: (List Bool)), bo.length = n -> f n k bo ≠ 0) (noninf: ∀(k: T) (bo: (List Bool)), f n k bo ≠ ⊤):(∏' (i : Fin ((l₁.length-1)+1)), f n (l₁[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) /
    (∏' (i : Fin ((l₂.length-1)+1)), f n (l₂[i.val]'(valid_index2 h2 i)) (x[i.val]'(valid_index3 h2 hy i)))  = f n (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) / f n (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) := by
    rw[tprod_fintype]
    rw[tprod_fintype]
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₁.length-1)+1)) => f n (l₁[b.val]'(valid_index2 h1 b)) (x[b.val]'(valid_index3 h1 hx b))) a.length]
    have ind: a.length < x.length := by
      rw[← hx]
      rw[h1]
      simp
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₂.length-1)+1)) => f n (l₂[b.val]'(valid_index2 h2 b)) (x[b.val]'(valid_index3 h2 hy b))) a.length]
    have helper: l₁.length - 1 = l₂.length - 1 := by aesop
    have hlp: (∏ i : Fin (l₁.length - 1), f n l₁[(Fin.succAbove a.length i).val] x[↑(Fin.succAbove a.length i).val]) = ∏ i : Fin (l₂.length - 1), f n l₂[(Fin.succAbove a.length i).val] x[(Fin.succAbove a.length i).val] := by
      apply Fintype.prod_equiv (Equiv.cast (congr_arg Fin helper))
      simp[succHelp l₁ l₂ h1 h2]
      intro i
      congr
      rw [← propext cast_eq_iff_heq]
      rw [← propext cast_eq_iff_heq]
    rw[hlp]
    rw[ENNReal.mul_div_mul_right]
    simp

    simp[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
    simp[mod_helper (a.length) (l₂.length) (by rw[h2];simp;linarith) (by rw[h2]; simp)]

    rw[Finset.prod_ne_zero_iff]
    intro i
    aesop
    rw[← lt_top_iff_ne_top]
    apply ENNReal.prod_lt_top
    intro i
    simp[noninf]

theorem reduction_final_RAP (n : Nat) (l₁ l₂: List T)(x: List (List Bool)) (f: Nat -> T → SLang (List Bool)) (h1: l₁ = a++[l]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length) (hx2 : ∀ i : Fin (l₂.length - 1 + 1), (x[i]'(by sorry)).length = n) (hy: l₂.length = x.length)(nonzero: ∀(k: T) (bo: (List Bool)), bo.length = n -> f n k bo ≠ 0)(noninf: ∀(k: T) (bo: (List Bool)), f n k bo ≠ ⊤):(∏' (i : Fin (l₁.length)), f n (l₁[i.val]'(by simp)) (x[i.val]'(by rw[← hx]; simp))) /
    (∏' (i : Fin (l₂.length)), f n (l₂[i.val]'(by simp)) (x[i.val]'(by rw[← hy];simp)))  = f n (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) / f n (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) := by
    have hl2: l₂.length ≥ 1 := by rw[h2];simp; linarith
    have hl1: l₁.length ≥ 1 := by rw[h1];simp; linarith
    rw[conversion_RAP l₂ x h2 hl2 hy (f n)]
    rw[conversion_RAP l₁ x h1 hl1 hx (f n)]
    rw [reduction2_RAP n l₁ l₂ x f h1 h2 hx hx2 hy nonzero noninf]

open Finset
open scoped BigOperators
