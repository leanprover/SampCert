import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Basic

/- Step 2 of the DP Proof: cancellation of probalities in the numerator and denominator. -/
lemma valid_index0 (l₁ : List T)(h1: l₁ = a++[n]++b) (i : Fin (l₁.length - 1)): (Fin.succAbove (a.length) i).val < l₁.length := by
  have hl : l₁.length - 1 + 1 = l₁.length := by
      rw [Nat.sub_add_cancel]
      rw [h1]
      simp
      linarith
  simp [Fin.succAbove]
  split
  simp [Fin.castSucc]
  {calc
  i.val < l₁.length - 1 := i.2
  _ < l₁.length := by aesop}
  {
    calc
    i.succ.val = i.val + 1 := by simp
    _ < l₁.length - 1 + 1 := by linarith[i.2]
    _ = l₁.length := by rw [hl]
  }

lemma valid_index1 (l₁ l₂ : List T)(h1: l₁ = a++[n]++b) (h2: l₂ = a++[m]++b) (i : Fin ((l₁.length - 1))): (Fin.succAbove (a.length) i).val < l₂.length := by
  have hl: l₁.length = l₂.length := by aesop
  rw[←hl]
  apply valid_index0
  exact h1

lemma mod_helper (a b: ℕ)(h1: b ≥ 1)(h2: a<b): a % (b-1+1) = a := by
  rw[Nat.mod_eq_of_lt]
  rw[Nat.sub_add_cancel]
  exact h2
  exact h1

lemma succHelp (l₁ l₂ : List T)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b): ∀i : Fin (l₁.length - 1), l₁[(Fin.succAbove a.length i).val]'(valid_index0 l₁ h1 i) = l₂[Fin.succAbove a.length i]'(valid_index1 l₁ l₂ h1 h2 i) := by
      intro i
      simp only [h1,h2]
      by_cases i < a.length

      case pos h =>
        unfold Fin.succAbove
        have h' : i.castSucc < ↑a.length := by
          rw [@Fin.castSucc_lt_iff_succ_le]
          rw [@Fin.le_iff_val_le_val]
          simp
          rw[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
          simp[Nat.succ_le_of_lt h]

        simp only[h']
        simp only [↓reduceIte, Fin.coe_castSucc,Fin.getElem_fin]
        rw[List.getElem_append_left (a++[n]) b (by simp[h];linarith)]
        rw[List.getElem_append_left a [n] h]
        rw[List.getElem_append_left (a++[m]) b (by simp[h];linarith)]
        rw[List.getElem_append_left]

      case neg h =>
        have iab: i.val - a.length < b.length := by
          have ile : i < l₁.length - 1 := i.is_lt
          simp[h1] at ile
          rw[tsub_lt_iff_left]
          exact ile
          simp at h
          exact h
        unfold Fin.succAbove
        have h' : ¬ i.castSucc < ↑a.length := by
          simp at h
          simp
          rw [@Fin.le_castSucc_iff]
          apply Nat.lt_succ_of_le
          simp
          rw[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
          exact h
        simp only[h']
        simp only [↓reduceIte, Fin.coe_castSucc,Fin.getElem_fin]
        rw[List.getElem_append_right (a++[n]) b (by simp;linarith)]
        rw[List.getElem_append_right (a++[m]) b (by simp;linarith)]
        simp
        simp
        linarith
        simp
        linarith


lemma valid_index2 {l₁ : List T} (h1: l₁ = a++[n]++b) (i : Fin ((l₁.length - 1) + 1)):
  i.val < l₁.length := by
    have hl1: l₁.length - 1 + 1 = l₁.length := by
      rw [Nat.sub_add_cancel]
      rw[h1]
      simp
      linarith
    exact Nat.lt_of_lt_of_eq i.2 hl1

lemma valid_index3 {β: Type}{l₁ : List T} {x : List β} (h1: l₁ = a++[n]++b) (hx: l₁.length = x.length) (i : Fin ((l₁.length - 1) + 1)):
  i.val < x.length := by
    rw[←hx]
    apply valid_index2 h1 i

lemma valid_index8 {β: Type}{l₁ : List T} {x : List β} (h1: l₁ = a++[n]++b) (hx: l₁.length = x.length) (i : Fin ((l₁.length - 1) + 1)):
  i.val < x.length := by
    rw[←hx]
    apply valid_index2 h1 i

lemma reduction2 {β: Type}(l₁ l₂: List T)(x: List β)(f: T → SLang β)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)
 (nonzero: ∀ (i : Fin (l₂.length - 1)), f (l₂[↑((@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove i)]'(by apply valid_index8 h2; aesop)) (x[↑((@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove i)]'(by apply valid_index8 h2; aesop)) ≠ 0)
 (noninf: ∀(k: T) (bo: β), f k bo ≠ ⊤):(∏' (i : Fin ((l₁.length-1)+1)), f (l₁[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) /
    (∏' (i : Fin ((l₂.length-1)+1)), f (l₂[i.val]'(valid_index2 h2 i)) (x[i.val]'(valid_index3 h2 hy i)))  = f (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) / f (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) := by
    rw[tprod_fintype]
    rw[tprod_fintype]
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₁.length-1)+1)) => f (l₁[b.val]'(valid_index2 h1 b)) (x[b.val]'(valid_index3 h1 hx b))) a.length]

    have ind: a.length < x.length := by
      rw[← hx]
      rw[h1]
      simp
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₂.length-1)+1)) => f (l₂[b.val]'(valid_index2 h2 b)) (x[b.val]'(valid_index3 h2 hy b))) a.length]
    have helper: l₁.length - 1 = l₂.length - 1 := by aesop
    have hlp: (∏ i : Fin (l₁.length - 1), f l₁[(Fin.succAbove a.length i).val] x[↑(Fin.succAbove a.length i).val]) = ∏ i : Fin (l₂.length - 1), f l₂[(Fin.succAbove a.length i).val] x[(Fin.succAbove a.length i).val] := by
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
    intro i _
    apply nonzero i
    rw[← lt_top_iff_ne_top]
    apply ENNReal.prod_lt_top
    intro i
    simp[noninf]

lemma fin_prod_cast {n m : ℕ} (h : n = m)(f : Fin n → ENNReal) :
  ∏' i : Fin n, f i = ∏' i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  simp

lemma conversion {β: Type}(l: List T) (x: List β)(h1: l = a++[n]++b)(hl : l.length ≥ 1)(hx: l.length = x.length)(f: T → SLang β): (∏' (i : Fin (l.length)), f (l[i.val]'(by simp)) (x[i.val]'(by rw[← hx];simp))) = (∏' (i : Fin ((l.length-1)+1)), f (l[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) := by
  rw [fin_prod_cast (by rw [← Nat.sub_add_cancel hl])]
  simp

theorem reduction_final {β: Type}(l₁ l₂ a b: List T)(n m : T)(x: List β)(f: T → SLang β)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)
   (nonzero: ∀ (i : Fin (l₂.length - 1)), f (l₂[↑((@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove i)]'(by apply valid_index8 h2; aesop)) (x[↑((@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove i)]'(by apply valid_index8 h2; aesop)) ≠ 0)
   (noninf: ∀(k: T) (bo: β), f k bo ≠ ⊤):(∏' (i : Fin (l₁.length)), f (l₁[i.val]'(by simp)) (x[i.val]'(by rw[← hx]; simp))) /
    (∏' (i : Fin (l₂.length)), f (l₂[i.val]'(by simp)) (x[i.val]'(by rw[← hy];simp)))  = f (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) / f (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) := by
    have hl2: l₂.length ≥ 1 := by rw[h2];simp; omega
    have hl1: l₁.length ≥ 1 := by rw[h1];simp; omega
    rw[conversion l₂ x h2 hl2 hy f]
    rw[conversion l₁ x h1 hl1 hx f]
    rw [reduction2 l₁ l₂ x f h1 h2 hx hy nonzero noninf]
