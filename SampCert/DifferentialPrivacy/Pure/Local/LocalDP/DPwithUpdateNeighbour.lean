import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithGeneralNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.UpdateNeighbour

open SLang
open Classical

namespace SLang

def DP_withUpdateNeighbour (m : Mechanism T U) (ε : ℝ) : Prop :=
 DP_withGeneralNeighbour m (UpdateNeighbour) ε

def DP_singleton_withUpdateNeighbour (m : Mechanism T U) (ε : ℝ) : Prop :=
  DP_singleton_withGeneralNeighbour m (UpdateNeighbour) ε
end SLang

theorem singleton_to_event_update (m : Mechanism T U) (ε : ℝ) (h : DP_singleton_withUpdateNeighbour m ε) :
  DP_withUpdateNeighbour m ε := by
  simp [DP_withUpdateNeighbour]
  simp [DP_singleton_withUpdateNeighbour] at h
  intros l₁ l₂ h1 S
  replace h1 := h l₁ l₂ h1
  have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0) / (if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal ε.exp := by
    aesop
  have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
    aesop
  have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
    intro b
    right
    simp
    exact Real.exp_pos ε
  have D := fun { x : U } => @ENNReal.div_le_iff_le_mul (if x ∈ S then m l₁ x else 0) (if x ∈ S then m l₂ x else 0) (ENNReal.ofReal ε.exp) (B (if x ∈ S then m l₂ x else 0)) (C (if x ∈ S then m l₂ x else 0))
  have E := fun x : U => D.1 (A x)
  have F := ENNReal.tsum_le_tsum E
  rw [ENNReal.tsum_mul_left] at F
  rw [← ENNReal.div_le_iff_le_mul] at F
  · clear h1 A B C D
    trivial
  · aesop
  · right
    simp
    exact Real.exp_pos ε

theorem event_to_singleton_update (m : Mechanism T U) (ε : ℝ)(h: DP_withUpdateNeighbour m ε):
  DP_singleton_withUpdateNeighbour m ε := by
  simp [DP_singleton_withUpdateNeighbour]
  intros l₁ l₂ h1 x
  replace h1 := h l₁ l₂ h1 {x}
  simp at h1
  rw [tsum_eq_single x] at h1
  · simp at h1
    rw [tsum_eq_single x] at h1
    · simp at h1
      trivial
    · aesop
  · aesop

theorem event_eq_singleton_update (m : Mechanism T U) (ε : ℝ) :
  DP_withUpdateNeighbour m ε ↔ DP_singleton_withUpdateNeighbour m ε := by
  constructor
  · apply event_to_singleton_update
  · apply singleton_to_event_update

lemma privPostProcess_DPwithUpdate_bound{nq : Mechanism T U} {ε : NNReal} (h : DP_withUpdateNeighbour nq ε) (f : U → V) :
  DP_withUpdateNeighbour (privPostProcess nq f) ε := by
  rw [event_eq_singleton_update] at *
  simp [DP_singleton_withUpdateNeighbour] at *
  intros l₁ l₂ neighbours x
  replace h := h l₁ l₂ neighbours
  simp [privPostProcess]
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum _ ENNReal.summable (by aesop)
  intro i
  split
  · rename_i h
    subst h
    refine (ENNReal.div_le_iff_le_mul ?inl.hb0 ?inl.hbt).mp (h i)
    · aesop
    · right
      simp
      exact Real.exp_pos ε
  · simp
