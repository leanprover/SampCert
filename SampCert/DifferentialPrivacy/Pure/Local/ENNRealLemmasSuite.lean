import SampCert

namespace ENNRealLemmas

lemma tsum_equal_comp {α β: Type} [AddCommMonoid β] [TopologicalSpace β] (f g : α -> β) (h: ∀i : α, f i = g i ):
   ∑' (i : α), f i = ∑' (i : α), g i := by simp_all

lemma ennreal_mul_eq (a b c : ENNReal): a = b -> c * a = c * b := by
  intro h
  rw[h]

lemma ennreal_mul_assoc (a b c : ENNReal): a * c + b * c = (a + b) * c := by ring

lemma le_add_non_zero (a b :ENNReal)(h: b ≠ 0)(h2: a ≠ ⊤): a < a+b := by
  rw [@lt_iff_le_and_ne]
  apply And.intro
  simp_all
  simp
  rw [Not]
  intro c
  have gg : a + 0 =a +b := by
    simp
    exact c
  rw [ENNReal.add_right_inj] at gg
  symm at gg
  subst gg
  have hh: (0 ≠ 0) → False := by simp
  apply hh
  exact_mod_cast h
  exact h2

lemma sub_le_add_ennreal (a b :ENNReal)(h1: b ≠ 0)(h3: b ≤ a)(h4: a ≠ ⊤): a -b < a +b := by
  apply ENNReal.sub_lt_of_lt_add
  exact h3
  rw [add_assoc]
  apply le_add_non_zero
  simp_all only [ne_eq, add_eq_zero, and_self, not_false_eq_true]
  exact h4

lemma mult_ne_zero (a b : ENNReal) (h1 : a ≠ 0) (h2 : b ≠ 0): a * b ≠ 0 := by aesop

lemma ineq_coercion (num : Nat) (den : PNat) (h : 2 * num < den):
2 * (@Nat.cast ENNReal NonAssocSemiring.toNatCast num) < @Nat.cast ENNReal CanonicallyOrderedCommSemiring.toNatCast ↑den :=
  by norm_cast

/- lemma mult_inv_dist (a b : ENNReal): (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [@inv_eq_one_div]
  rw [@inv_eq_one_div]
  rw [@inv_eq_one_div]
  sorry
-/

lemma mult_ne_zero_inv (a b : ENNReal) (h1 : a ≠ T) (h2 : b ≠ T): (a * b)⁻¹ ≠ 0 := by sorry


#check ENNReal.mul_eq_top

lemma mult_ne_top (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ ⊤): a * b ≠ ⊤ := by
  rw [@Ne.eq_def]
  intro h
  rw [ENNReal.mul_eq_top] at h
  cases h with
  | inl h =>
   apply And.right at h
   contradiction
  | inr h =>
   apply And.left at h
   contradiction

lemma Finset.prod_ne_top (n : Nat) (f : ℕ -> ENNReal) (h : ∀ i, f i ≠ ⊤):
  ∏ (i : Fin n), f i.val ≠ ⊤ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [@Fin.prod_univ_add]
    apply mult_ne_top
    apply ih
    rw [@Fin.prod_univ_one]
    apply h

lemma Finset.prod_ne_top_fin (n : Nat) (f : Fin n -> ENNReal) (h : ∀ i, f i ≠ ⊤):
  ∏ (i : Fin n), f i ≠ ⊤ := by
  cases hn : n == 0 with
| false =>
  have hn1: n > 0 := by
     simp at hn
     exact Nat.zero_lt_of_ne_zero hn

  let g : Nat -> ENNReal := fun i => f (Fin.ofNat' i hn1)
  have mod: ∀ i : Fin n, i % n = i := by
    intro i
    rw [Nat.mod_eq]
    simp
  have h0: ∀ i : Fin n, f i = g i := by
    intro i
    simp_all [g]
    have eq: Fin.ofNat' (i.val) hn1 = i := by
      simp_all [Fin.ofNat']
    rw [eq]
  have h1: ∏ i : Fin n, f i = ∏ i : Fin n, g i := by
    conv =>
      enter [2, 2, i]
      rw [←h0 i]
  have h2: ∀ i : ℕ, g i ≠ ⊤ := by
    intro i
    apply h
  rw [h1]
  apply Finset.prod_ne_top n g
  exact h2
 | true =>
   simp at hn
   subst hn
   simp


lemma div_ne_top (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ 0): a / b ≠ ⊤ := by
  simp
  rw [Not]
  intro a
  rw [@ENNReal.div_eq_top] at a
  rcases a with ⟨_,ar⟩
  subst ar
  simp_all only [ne_eq, not_true_eq_false]
  rename_i h3
  rcases h3 with ⟨hl,_⟩
  subst hl
  simp_all only [ne_eq, not_true_eq_false]

lemma div_div_cancel (a b c : ENNReal) (h : c ≠ 0 ∧ c ≠ ⊤): a/c = b/c -> a = b := by
  intro h1
  sorry

lemma div_div_cancel_rev (a b c : ENNReal) (h : c ≠ 0 ∧ c ≠ ⊤): a < b -> a / c < b / c := by
  intro h1
  apply ENNReal.div_lt_of_lt_mul
  rw [@ENNReal.mul_comm_div]
  rw [ENNReal.div_self]
  simp
  exact h1
  exact h.left
  exact h.right



lemma quot_gt_one_rev (a b : ENNReal): b < a -> 1 < a/b := by
  cases hb : b == 0 with
  | true => simp at hb
            subst hb
            intro ha
            have h1 : a / 0 = ⊤ := by
              rw [@ENNReal.div_eq_top]
              apply Or.inl
              apply And.intro
              aesop
              trivial
            rw [h1]
            decide
  | false => simp at hb
             intro ha
             have h1: b/b = 1 := by
              rw [ENNReal.div_self]
              aesop
              aesop
             cases hbT : b == ⊤ with
            | true =>
              simp at hbT
              aesop
            | false =>
              simp at hbT
              have h2: b/b < a/b := by
               apply div_div_cancel_rev b a b
               aesop
               exact ha
              rw[h1] at h2
              exact h2

lemma quot_gt_one (a b : ENNReal): 1 < a/b -> b < a := by
  intro h
  cases hb: b == 0 with
  | true => simp at hb
            cases ha: a == 0 with
            | true => simp at ha
                      subst hb
                      subst ha
                      apply False.elim
                      have nh: ¬ (1 : ENNReal)  < 0/0 := by simp
                      contradiction
            | false => simp at ha
                       have ha1: a > 0 := by exact pos_iff_ne_zero.mpr ha
                       rw[←hb] at ha1
                       exact ha1
  | false => simp at hb
             cases hbT : b == ⊤ with
            | true => simp at hbT
                      subst hbT
                      have h1 : ¬ 1 < a / ⊤ := by simp_all only [ENNReal.div_top, not_lt_zero']
                      apply False.elim
                      apply h1
                      exact h
            | false =>
              simp at hbT
              have h1: 1 * b < (a / b) * b := ENNReal.mul_lt_mul_right' hb hbT h
              rw [@ENNReal.mul_comm_div] at h1
              rw [ENNReal.div_self] at h1
              rw [@CanonicallyOrderedCommSemiring.one_mul] at h1
              rw [@CanonicallyOrderedCommSemiring.mul_one] at h1
              exact h1
              apply hb
              apply hbT

lemma div_ineq_flip (a b c : ENNReal): a / b > c -> b / a < c := by sorry

lemma quot_lt_one_rev (a b : ENNReal): b < a -> b/a < 1 := by
  intro h
  apply div_ineq_flip
  exact quot_gt_one_rev a b h

lemma tsum_func_zero_simp (f : List Bool -> ENNReal) (h : f [] = 0):
  ∑' (x : List Bool), f x = (∑'(x : List Bool), if x = [] then 0 else f x) := by
    rw [ENNReal.tsum_eq_add_tsum_ite []]
    simp [h]
    apply tsum_equal_comp
    intro i
    aesop

lemma tsum_ite_not (f : List Bool -> ENNReal):
  ∑' (x : List Bool), (if x = [] then 0 else f x) =
  ∑' (x : List Bool), if assm : x ≠ [] then f x else 0 := by simp_all [ite_not]

lemma tsum_ite_mult (f : T -> ENNReal) (P : T -> Bool):
  (∑' (x : T), f x * if (P x) then 1 else 0) = ∑' (x : T), if (P x) then f x else 0 := by simp_all only [mul_ite,
    mul_one, mul_zero]

lemma sub_add_eq_add_sub (a b :ENNReal)(h : b ≤ a)(h1 : b ≠ ⊤): a - b+ b = a + b-b := by
  rw [@AddCommMonoidWithOne.add_comm]
  rw [add_tsub_cancel_of_le h]
  rw [@AddCommMonoidWithOne.add_comm]
  symm
  apply ENNReal.sub_eq_of_add_eq
  exact h1
  rw [add_comm]

lemma sub_add_cancel_ennreal (a b :ENNReal)(h:b≤ a)(h1 : b ≠ ⊤): a -b +b =a := by
  rw [sub_add_eq_add_sub]
  rw [ENNReal.add_sub_cancel_right h1]
  exact h
  exact h1


lemma le_double (a b c : ENNReal)(h1 : a ≤ b)(h2 : c ≤ d)(htop1: a ≠ ⊤)(htop2 : c ≠ ⊤): a * c ≤ b * d := by
  rw [@Decidable.le_iff_eq_or_lt]
  rw [@Decidable.le_iff_eq_or_lt] at h1
  rw [@Decidable.le_iff_eq_or_lt] at h2
  cases h1 with
  | inl h1l =>
    cases h2 with
    | inl h2l =>
      left
      rw [h1l]
      rw [h2l]
    | inr h2r =>
      cases bzero : b == 0 with
      | true =>
        left
        subst h1l
        simp_all only [ne_eq, not_false_eq_true, beq_iff_eq, zero_mul]
      | false =>
        right
        subst h1l
        simp_all only [beq_eq_false_iff_ne]
        rw [propext (ENNReal.mul_lt_mul_left bzero htop1)]
        exact h2r
  | inr hr =>
    cases h2 with
    | inl h2l =>
      rw [← h2l]
      cases czero : c == 0 with
      | true =>
         left
         subst h2l
         simp_all only [ne_eq, beq_iff_eq, mul_zero]
      | false =>
        right
        rw [@beq_eq_false_iff_ne] at czero
        rw [propext (ENNReal.mul_lt_mul_right czero htop2)]
        exact hr
    | inr h2r =>
      right
      apply ENNReal.mul_lt_mul
      exact hr
      exact h2r

lemma exp_change_form (num : Nat) (den : PNat) (h: 2 * num < den) : ((2:ENNReal)⁻¹ + num / den) / (2⁻¹ - num / den) = (↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num) := by sorry


end ENNRealLemmas
