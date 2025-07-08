import SampCert

open SLang

instance SLang.LawfulMonad : LawfulMonad SLang where
  map_const := by
               intro a b
               rfl
  id_map := by
            intro u hu
            rw [@Function.funext_iff]
            intro a
            unfold id
            sorry
  seqLeft_eq := by
    intro α β x y
    sorry
  seqRight_eq := by
    intro α β x y
    sorry
  pure_seq := by
    intro α β g x
    simp_all only [pure]
    sorry
  pure_bind := by simp
  bind_pure_comp := by
    intro α β f x
    simp_all only [bind, pure]
    apply Eq.refl
  bind_assoc := by simp
  bind_map := by
    intro α β f x
    simp_all only [bind]
    apply Eq.refl
