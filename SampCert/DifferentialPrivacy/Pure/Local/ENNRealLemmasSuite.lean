import SampCert

namespace ENNRealLemmas

lemma tsum_equal_comp {α β: Type} [AddCommMonoid β] [TopologicalSpace β] (f g : α -> β) (h: ∀i : α, f i = g i ):
   ∑' (i : α), f i = ∑' (i : α), g i := by simp_all

lemma ennreal_mul_eq (a b c : ENNReal): a = b -> c * a = c * b := by
  intro h
  rw[h]

lemma ennreal_mul_assoc (a b c : ENNReal): a * c + b * c = (a + b) * c := by ring

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
