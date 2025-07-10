import SampCert

noncomputable def f : List Bool -> ENNReal := fun b =>
  match b with
  | [] => 1
  | x :: _ => if x then 0 else 0

lemma f_sums_to_1: ∑' (b : List Bool), (if assm: b ≠ [] then f b else 1) = 1 := by
  rw [ENNReal.tsum_eq_add_tsum_ite []]
  convert show (1 + 0 : ENNReal) = 1 from add_zero 1
  rw [ENNReal.tsum_eq_zero]
  intro b
  by_cases h : b = []
  · simp [h]
  · unfold f; aesop

lemma silly: (∑' (b : List Bool), if b = [true] then 1 else 0) = 1 := by
  rw [@tsum_ite_eq]


lemma silly2 (f : Bool -> ENNReal): (∑' (b : List Bool), if b = [true] then f true else if b = [false] then f false else 0)
= f true + f false := by sorry 
