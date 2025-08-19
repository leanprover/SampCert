import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Generic
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Prod

noncomputable section

open Classical Set

namespace SLang


def privPostProcessRand {T U V : Type} (nq : Mechanism T U) (g : U → PMF V) : Mechanism T V :=
  fun l => (nq l).bind g

lemma tsum_ite_eq_single {T U : Type} (m : Mechanism T U) (l₁ : List T)(u : U):
  (∑' (x : U), if x = u then ((m l₁) x) else 0) = (m l₁) u := by
  classical
  have hpoint :
    (fun x : U => if x = u then (m l₁) x else 0) =
    (fun x : U => if x = u then (m l₁) u else 0) := by
    funext x
    by_cases hx : x = u
    · simp [hx]
    · simp [hx]
  have hcollapse : (∑' x : U, if x = u then (m l₁) u else 0) = (m l₁) u := by
    simp [tsum_ite_eq (β := U) (α := ENNReal) u ((m l₁) u)]
  simp [hpoint, hcollapse]


lemma DP.pointwise_ratio_bound {T U : Type}
    {m : Mechanism T U} {ε : ℝ}
    (h : DP m ε) {l₁ l₂ : List T} (hN : Neighbour l₁ l₂) :
    ∀ u : U, m l₁ u ≤ ENNReal.ofReal (Real.exp ε) * m l₂ u := by
  intro u
  have hS := h l₁ l₂ hN ({u} : Set U)
  have hnum :
      (∑' x : U, (if x ∈ ({u} : Set U) then m l₁ x else 0)) = m l₁ u := by
    classical
    have : (fun x : U => if x ∈ ({u} : Set U) then m l₁ x else 0)
           = (fun x : U => if x = u then m l₁ u else 0) := by
      funext x
      by_cases hx : x = u
      · subst hx; simp
      · simp [Set.mem_singleton_iff, hx]
    simpa [this] using (tsum_ite_eq_single m l₁ u)
  have hden :
      (∑' x : U, (if x ∈ ({u} : Set U) then m l₂ x else 0)) = m l₂ u := by
    classical
    have : (fun x : U => if x ∈ ({u} : Set U) then m l₂ x else 0)
           = (fun x : U => if x = u then m l₂ u else 0) := by
      funext x
      by_cases hx : x = u
      · subst hx; simp
      · simp [Set.mem_singleton_iff, hx]
    simpa [this] using (tsum_ite_eq_single m l₂ u)
  have hratio : m l₁ u / m l₂ u ≤ ENNReal.ofReal (Real.exp ε) := by
    rw [hnum, hden] at hS
    exact hS
  by_cases hz : m l₂ u = 0
  · have hfin : ENNReal.ofReal (Real.exp ε) ≠ ⊤ := by aesop
    have hzero : m l₁ u = 0 := by
      by_contra hpos
      have htop : m l₁ u / m l₂ u = ⊤ := by
        exact ENNReal.div_eq_top.mpr (Or.inl ⟨by simp [hpos], hz⟩)
      have : (⊤ : ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
        simp at hratio
        aesop
      have : ENNReal.ofReal (Real.exp ε) = ⊤ := top_le_iff.mp this
      exact hfin this
    simp [hz, hzero, zero_mul]
  · have h_not_infty : ⊤ ≠ m l₂ u := by
      have hle : m l₂ u ≤ 1 := by simpa using (m l₂).coe_le_one u
      have hlt : m l₂ u < ⊤ := lt_of_le_of_lt hle (by simp)
      aesop
    have : m l₁ u ≤ ENNReal.ofReal (Real.exp ε) * m l₂ u := by
      rw [← ENNReal.div_le_iff_le_mul]
      · exact hratio
      · aesop
      · aesop
    simpa using this



lemma tsum_indicator_mul_left {U V : Type} (p : PMF U) (g : U → PMF V) (S : Set V) (u : U) (hsplit : (fun v => if v ∈ S then p u * g u v else 0) = fun v => p u * if v ∈ S then g u v else 0):
(∑' v : V, if v ∈ S then p u * g u v else 0) = p u * ∑' v : V, if v ∈ S then (g u) v else 0:= by
    calc
  (∑' v : V, if v ∈ S then p u * g u v else 0)
      = ∑' v : V, p u * (if v ∈ S then g u v else 0) := by
        simp [hsplit]
  _ = p u * ∑' v : V, (if v ∈ S then g u v else 0) := by
        simpa using
          (ENNReal.tsum_mul_left
            (a := p u)
            (f := fun v : V => if v ∈ S then g u v else 0))

lemma tsum_bind_indicator {U V : Type}
    (p : PMF U) (g : U → PMF V) (S : Set V) :
    (∑' v : V, if v ∈ S then (p.bind g) v else 0) = (∑' u : U, p u * (∑' v : V, if v ∈ S then g u v else 0)) := by
    classical
  have hbind : ∀ v, (p.bind g) v = ∑' u, p u * g u v := by
    intro v; simp [PMF.bind_apply]
  calc
    (∑' v : V, if v ∈ S then (p.bind g) v else 0)
        = ∑' v, if v ∈ S then (∑' u, p u * g u v) else 0 := by
              simp [hbind]
    _   = ∑' v, ∑' u, (if v ∈ S then p u * g u v else 0) := by
              refine tsum_congr ?_
              intro v; by_cases hv : v ∈ S <;> simp [hv]
    _   = ∑' u, ∑' v, (if v ∈ S then p u * g u v else 0) := by
              simpa using
                ENNReal.tsum_comm (f := fun v u => (if v ∈ S then p u * g u v else 0))
    _   = ∑' u, p u * (∑' v, if v ∈ S then g u v else 0) := by
              refine tsum_congr ?_
              intro u
              have hsplit :(fun v => if v ∈ S then p u * g u v else 0) = (fun v => p u * (if v ∈ S then g u v else 0)) := by
                funext v; by_cases hv : v ∈ S <;> simp [hv, mul_comm, mul_left_comm, mul_assoc]
              exact tsum_indicator_mul_left p g S u hsplit

lemma randPostProcess_DP_bound {T U V : Type} {nq : Mechanism T U} {ε : NNReal} (h : PureDP nq ε) (g : U → PMF V) :
  DP (privPostProcessRand nq g) ε := by
  intro l₁ l₂ hN S
  let p₁ := nq l₁
  let p₂ := nq l₂
  let w : U → ENNReal := fun u => (∑' v : V, if v ∈ S then g u v else 0)
  have hNum : (∑' v : V, if v ∈ S then (privPostProcessRand nq g l₁) v else 0)
              = ∑' u : U, p₁ u * w u := by
    simpa [privPostProcessRand, p₁] using tsum_bind_indicator (nq l₁) g S
  have hDen : (∑' v : V, if v ∈ S then (privPostProcessRand nq g l₂) v else 0)
              = ∑' u : U, p₂ u * w u := by
    simpa [privPostProcessRand, p₂] using tsum_bind_indicator (nq l₂) g S
  have hpt := DP.pointwise_ratio_bound (T:=T) (U:=U) (m:=nq) (ε:=ε) h hN
  have hsum :
      (∑' u : U, p₁ u * w u)
      ≤ ENNReal.ofReal (Real.exp ε) * (∑' u : U, p₂ u * w u) := by
      have hpt' : ∀ u, p₁ u * w u ≤ (ENNReal.ofReal (Real.exp ε) * p₂ u) * w u := by
        intro u
        have := hpt u
        have hpt' : p₁ u ≤ ENNReal.ofReal (Real.exp ε) * p₂ u := by simpa [p₁, p₂] using hpt u
        have hw0 : 0 ≤ w u := by aesop
        have hmul : p₁ u * w u ≤ (ENNReal.ofReal (Real.exp ε) * p₂ u) * w u := mul_le_mul_of_nonneg_right hpt' hw0
        simpa [mul_left_comm, mul_comm, mul_assoc] using hmul
      have := ENNReal.tsum_le_tsum hpt'
      simpa [ENNReal.tsum_mul_left, mul_left_comm, mul_assoc] using this
  by_cases hDen0 : (∑' u : U, p₂ u * w u) = 0
  · have hNum0 : (∑' u : U, p₁ u * w u) = 0 := by
      have : (∑' u : U, p₁ u * w u) ≤ ENNReal.ofReal (Real.exp ε) * 0 := by simpa [hDen0] using hsum
      exact le_antisymm (le_trans this (by aesop)) (by exact bot_le)
    simp [hNum, hDen, hNum0, hDen0]
  · nth_rewrite 1 [mul_comm] at hsum
    have : (∑' u : U, p₁ u * w u) / (∑' u : U, p₂ u * w u) ≤ ENNReal.ofReal (Real.exp ε) := by (exact ENNReal.div_le_of_le_mul' hsum)
    simpa [hNum, hDen] using this


lemma DP.pointwise_ratio_bound_for_UpdateNeighbour {T U : Type}
    {m : Mechanism T U} {ε : ℝ}
    (h : DP_withUpdateNeighbour m ε) {l₁ l₂ : List T} (hN : UpdateNeighbour l₁ l₂) :
    ∀ u : U, m l₁ u ≤ ENNReal.ofReal (Real.exp ε) * m l₂ u := by
      intro u
      have hS := h l₁ l₂ hN ({u} : Set U)
      have hnum : (∑' x : U, (if x ∈ ({u} : Set U) then m l₁ x else 0)) = m l₁ u := by
        classical
        have : (fun x : U => if x ∈ ({u} : Set U) then m l₁ x else 0)
           = (fun x : U => if x = u then m l₁ u else 0) := by
          funext x
          by_cases hx : x = u
          · subst hx; simp
          · simp [Set.mem_singleton_iff, hx]
        simpa [this] using (tsum_ite_eq_single m l₁ u)
      have hden : (∑' x : U, (if x ∈ ({u} : Set U) then m l₂ x else 0)) = m l₂ u := by
        classical
        have : (fun x : U => if x ∈ ({u} : Set U) then m l₂ x else 0)
           = (fun x : U => if x = u then m l₂ u else 0) := by
          funext x
          by_cases hx : x = u
          · subst hx; simp
          · simp [Set.mem_singleton_iff, hx]
        simpa [this] using (tsum_ite_eq_single m l₂ u)
      have hratio : m l₁ u / m l₂ u ≤ ENNReal.ofReal (Real.exp ε) := by
        rw [hnum, hden] at hS
        exact hS
      by_cases hz : m l₂ u = 0
      · have hfin : ENNReal.ofReal (Real.exp ε) ≠ ⊤ := by aesop
        have hzero : m l₁ u = 0 := by
          by_contra hpos
          have htop : m l₁ u / m l₂ u = ⊤ := by
            exact ENNReal.div_eq_top.mpr (Or.inl ⟨by simp [hpos], hz⟩)
          have : (⊤ : ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
            simp at hratio
            aesop
          have : ENNReal.ofReal (Real.exp ε) = ⊤ := top_le_iff.mp this
          exact hfin this
        simp [hz, hzero, zero_mul]
      · have h_not_infty : ⊤ ≠ m l₂ u := by
          have hle : m l₂ u ≤ 1 := by simpa using (m l₂).coe_le_one u
          have hlt : m l₂ u < ⊤ := lt_of_le_of_lt hle (by simp)
          aesop
        have : m l₁ u ≤ ENNReal.ofReal (Real.exp ε) * m l₂ u := by
          rw [← ENNReal.div_le_iff_le_mul]
          · exact hratio
          · aesop
          · aesop
        simpa using this

lemma randPostProcess_DP_bound_with_UpdateNeighbour {T U V : Type} {nq : Mechanism T U} {ε : NNReal} (h : DP_withUpdateNeighbour nq ε) (g : U → PMF V) :
  DP_withUpdateNeighbour (privPostProcessRand nq g) ε := by
  intro l₁ l₂ hN S
  let p₁ := nq l₁
  let p₂ := nq l₂
  let w : U → ENNReal := fun u => (∑' v : V, if v ∈ S then g u v else 0)
  have hNum : (∑' v : V, if v ∈ S then (privPostProcessRand nq g l₁) v else 0)
              = ∑' u : U, p₁ u * w u := by
    simpa [privPostProcessRand, p₁] using tsum_bind_indicator (nq l₁) g S
  have hDen : (∑' v : V, if v ∈ S then (privPostProcessRand nq g l₂) v else 0)
              = ∑' u : U, p₂ u * w u := by
    simpa [privPostProcessRand, p₂] using tsum_bind_indicator (nq l₂) g S
  have hpt := DP.pointwise_ratio_bound_for_UpdateNeighbour (T:=T) (U:=U) (m:=nq) (ε:=ε) h hN
  have hsum :
      (∑' u : U, p₁ u * w u)
      ≤ ENNReal.ofReal (Real.exp ε) * (∑' u : U, p₂ u * w u) := by
      have hpt' : ∀ u, p₁ u * w u ≤ (ENNReal.ofReal (Real.exp ε) * p₂ u) * w u := by
        intro u
        have := hpt u
        have hpt' : p₁ u ≤ ENNReal.ofReal (Real.exp ε) * p₂ u := by simpa [p₁, p₂] using hpt u
        have hw0 : 0 ≤ w u := by aesop
        have hmul : p₁ u * w u ≤ (ENNReal.ofReal (Real.exp ε) * p₂ u) * w u := mul_le_mul_of_nonneg_right hpt' hw0
        simpa [mul_left_comm, mul_comm, mul_assoc] using hmul
      have := ENNReal.tsum_le_tsum hpt'
      simpa [ENNReal.tsum_mul_left, mul_left_comm, mul_assoc] using this
  by_cases hDen0 : (∑' u : U, p₂ u * w u) = 0
  · have hNum0 : (∑' u : U, p₁ u * w u) = 0 := by
      have : (∑' u : U, p₁ u * w u) ≤ ENNReal.ofReal (Real.exp ε) * 0 := by simpa [hDen0] using hsum
      exact le_antisymm (le_trans this (by aesop)) (by exact bot_le)
    simp [hNum, hDen, hNum0, hDen0]
  · nth_rewrite 1 [mul_comm] at hsum
    have : (∑' u : U, p₁ u * w u) / (∑' u : U, p₂ u * w u) ≤ ENNReal.ofReal (Real.exp ε) := by (exact ENNReal.div_le_of_le_mul' hsum)
    simpa [hNum, hDen] using this
