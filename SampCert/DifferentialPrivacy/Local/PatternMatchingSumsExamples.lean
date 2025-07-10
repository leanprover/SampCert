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

lemma f_sums_to_1': ∑' (b : List Bool), (if assm: b ≠ [] then f b else 1) = 1 := by
  conv =>
    enter [1, 1, b]
    rw [← List.head_cons_tail b assm, f]
  simp
