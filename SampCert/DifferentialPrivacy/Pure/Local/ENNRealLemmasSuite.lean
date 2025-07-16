import SampCert

namespace ENNRealLemmas

lemma tsum_equal_comp {α β: Type} [AddCommMonoid β] [TopologicalSpace β] (f g : α -> β) (h: ∀i : α, f i = g i ):
   ∑' (i : α), f i = ∑' (i : α), g i := by simp_all

lemma ennreal_mul_eq (a b c : ENNReal): a = b -> c * a = c * b := by
  intro h
  rw[h]

lemma ennreal_mul_assoc (a b c : ENNReal): a * c + b * c = (a + b) * c := by ring

lemma mult_ne_zero (a b : ENNReal) (h1 : a ≠ 0) (h2 : b ≠ 0): a * b ≠ 0 := by aesop

lemma mult_inv_dist (a b : ENNReal): (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [@inv_eq_one_div]
  rw [@inv_eq_one_div]
  rw [@inv_eq_one_div]
  sorry

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

end ENNRealLemmas
