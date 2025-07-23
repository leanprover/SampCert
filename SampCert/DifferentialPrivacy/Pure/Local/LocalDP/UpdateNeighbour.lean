import SampCert

namespace SLang

/- Lists which differ by update of a single entry. -/
inductive UpdateNeighbour {T : Type} (l₁ l₂ : List T) : Prop where
  | Update: l₁ = a ++ [n] ++ b → l₂ = a ++ [m] ++ b -> UpdateNeighbour l₁ l₂

/-
UpdateNeighbour relation is symmetric.
-/
def UpdateNeighbour_symm (l₁ l₂ : List T) (H : UpdateNeighbour l₁ l₂) : UpdateNeighbour l₂ l₁ := by
  cases H
  · rename_i _ _ _ _ Hl1 Hl2
    exact UpdateNeighbour.Update Hl2 Hl1

lemma UpdateNeighbour_length {T : Type} {l₁ l₂ : List T} (H : UpdateNeighbour l₁ l₂) :
  l₁.length = l₂.length := by
  cases H
  rename_i _ _ _ _ Hl1 Hl2
  rw[Hl1, Hl2]
  simp
  
end SLang
