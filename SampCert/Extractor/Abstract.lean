/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

-- Is this correctly bundled? Using this structure seems challenging. Feels like the monad should be in place of T.
class Capsid (T : Type) where
  CapsM : Type → Type
  CapsM_inst : Monad CapsM

  capsWhile : (T → Bool) → (T → CapsM T) → (init : T) → CapsM T

def ret_false_test [C : Capsid T] : C.CapsM Bool := C.CapsM_inst.pure False

class Capsid_semibundled (CapsM : Type u -> Type v) extends Monad CapsM where
  capsWhile : (T → Bool) → (T → CapsM T) → (init : T) → CapsM T

def ret_false_test' [Capsid_semibundled CapsM] : CapsM Bool := return false






/-
Finite unrolling of a loop with a signal for max depth reached
-/




-- def iter [Monad m] (body : T -> m T) (cond : T -> Bool) (fuel : Nat) (t : T) : (OptionT m) T
--   := match fuel with
--      | Nat.zero => failure
--      | Nat.succ fuel' =>
--         if cond t
--           then (body t) >>= (iter body cond fuel')
--           else pure t
