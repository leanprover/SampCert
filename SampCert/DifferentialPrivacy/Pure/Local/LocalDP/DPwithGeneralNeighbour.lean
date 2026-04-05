import SampCert.DifferentialPrivacy.Generic
namespace SLang

open SLang
open Classical

/- DP with a general neighbour relation.
   The definition of the neighbour relation is passed in as a parameter.-/
def DP_withGeneralNeighbour (m : Mechanism T U) (VariableNeighbour: List T -> List T -> Prop) (ε : ℝ): Prop :=
  ∀ l₁ l₂ : List T, VariableNeighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) / (∑' x : U, if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal (Real.exp ε)

/- Instantiation of PureDP with a general neighbour relation. -/
def PureDP_withGeneralNeighbour (m : Mechanism T U) (VariableNeighbour : List T -> List T -> Prop) (ε : NNReal) : Prop :=
  DP_withGeneralNeighbour m VariableNeighbour ε

/- Instantiation of DP_singleton with a general neighbour relation. -/
def DP_singleton_withGeneralNeighbour (m : Mechanism T U) (VariableNeighbour: List T -> List T -> Prop) (ε : ℝ): Prop :=
  ∀ l₁ l₂ : List T, VariableNeighbour l₁ l₂ → ∀ x : U,
  (m l₁ x) / (m l₂ x) ≤ ENNReal.ofReal (Real.exp ε)

end SLang
