import SampCert

open SLang

instance SLang.LawfulMonad : LawfulMonad SLang where
  map_const := by
               intro a b
               rfl
  id_map := by
            intro u hu
            simp [Functor.map]
  seqLeft_eq := by
    intro α β x y
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map]
    apply Eq.refl
  seqRight_eq := by
    intro α β x y
    simp [SeqRight.seqRight, Seq.seq, Functor.map]
  pure_seq := by
    intro α β g x
    simp [Seq.seq, Functor.map]
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
