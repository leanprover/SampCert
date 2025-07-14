import SampCert

namespace SLang

/- Lists which differ by update of a single entry. -/
inductive UpdateNeighbour (l₁ l₂ : List T) : Prop where
  | Update: l₁ = a ++ [n] ++ b → l₂ = a ++ [m] ++ b -> UpdateNeighbour l₁ l₂

/-
UpdateNeighbour relation is symmetric.
-/
def UpdateNeighbour_symm (l₁ l₂ : List T) (H : UpdateNeighbour l₁ l₂) : UpdateNeighbour l₂ l₁ := by
  cases H
  · rename_i _ _ _ _ Hl1 Hl2
    exact UpdateNeighbour.Update Hl2 Hl1

end SLang
