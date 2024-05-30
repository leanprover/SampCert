/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

-- class Capsid (T : Type) (M : Type -> Type) where
--   CapsidM_inst : Monad M
--   capsWhile :  (T → Bool) → (T → M T) → (init : T) → M T


class Capsid (CapsM : Type u -> Type v) extends Monad CapsM where
  capsWhile : (cond : T → Bool) → (body : T → CapsM T) → T → CapsM T


section capsid_wf
  variable {CapsM : Type u -> Type v} [C : Capsid CapsM]
  variable {T : Type u}
  variable (cond : T -> Bool) (body : T -> CapsM T)

  open Capsid

  def capsIter (fuel : Nat) : T -> (OptionT CapsM) T
    := fun t =>
       match fuel with
       | Nat.zero => failure
       | Nat.succ fuel' =>
          if cond t
            then (body t) >>= (capsIter fuel')
            else pure t

  def capsIterPartial (fuel : Nat) : T -> CapsM T
    := fun t =>
       match fuel with
       | Nat.zero => return t
       | Nat.succ fuel' =>
          if cond t
            then (body t) >>= (capsIterPartial fuel')
            else pure t

  -- Partial correctness specification for While
  -- Since we're going to translate it into a while loop, we want specify that the shallow embedding to behave like a
  -- the limit of loop iterations.
  def CapsWhileSpec : Prop
    := ∀ t0, capsWhile cond body t0 = sorry
--         ∀ t0 : T, ∃ i : Nat, ((∀ j : Nat, j < i -> iter body cond j t0 = failure) ∧ ¬ (iter body cond i t0 = failure))
--     -> iter body cond i t0 = loop T body cond t0
--     Err... This is not right. Maybe we require that the well-formed Capsid instances are topological types?
--     Do we want to say that "terminating executions of loops equal a finite unrolling" or "loops are the
--     limit of finite unrollings"?

end capsid_wf

class CapsidWF (CapsM : Type u -> Type v) extends Capsid CapsM where
  capsWhileWF : ∀ (cond : T -> Bool), ∀ (body : T -> CapsM T), CapsWhileSpec cond body
