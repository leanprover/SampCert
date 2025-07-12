import SampCert

namespace SLang

open SLang
open Classical

def DP_withGeneralNeighbour (m : Mechanism T U) (VariableNeighbour: List T -> List T -> Prop) (ε : ℝ): Prop :=
  ∀ l₁ l₂ : List T, VariableNeighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) / (∑' x : U, if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal (Real.exp ε)

def PureDP_withGeneralNeighbour (m : Mechanism T U) (VariableNeighbour : List T -> List T -> Prop) (ε : NNReal) : Prop :=
  DP_withGeneralNeighbour m VariableNeighbour ε

end SLang
