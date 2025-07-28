import SampCert

namespace ENNRealLemmas

lemma tsum_equal_comp {α β: Type} [AddCommMonoid β] [TopologicalSpace β] (f g : α -> β) (h: ∀i : α, f i = g i ):
   ∑' (i : α), f i = ∑' (i : α), g i := by simp_all

lemma ennreal_mul_eq (a b c : ENNReal): a = b -> c * a = c * b := by
  intro h
  rw[h]

lemma ennreal_mul_assoc (a b c : ENNReal): a * c + b * c = (a + b) * c := by ring

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


lemma mult_ne_top (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ ⊤): a * b ≠ ⊤ := by
  rw [← @ENNReal.inv_ne_zero]
  rw [← @ENNReal.inv_ne_zero] at h1
  rw [← @ENNReal.inv_ne_zero] at h2
  sorry

lemma div_ne_top (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ 0): a / b ≠ ⊤ := by
  rw [← @ENNReal.inv_ne_zero]
  rw [← @ENNReal.inv_ne_zero] at h1
  rw [@ENNReal.div_eq_inv_mul]
  sorry

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


end ENNRealLemmas
