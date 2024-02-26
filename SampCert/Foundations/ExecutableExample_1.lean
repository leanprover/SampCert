/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

open Nat

def PMF := Bool → Float

instance : Repr PMF where
  reprPrec := λ p : PMF => λ _ => s!"[T -> {p True} , F -> {p False}]"

def pure (a : Bool) : PMF :=
  fun a' => if a' = a then 1 else 0

def bind (p : PMF) (f : Bool → PMF) : PMF :=
  fun b =>  p true * f true b + p false * f false b

def bottom : PMF := λ _ => 0

def WhileFunctional (cond : Bool → Bool) (body : Bool → PMF) (wh : Bool → PMF) : Bool → PMF :=
  λ a : Bool =>
  if cond a
  then bind (body a) (λ v => wh v)
  else pure a

def prob_while_cut (cond : Bool → Bool) (body : Bool → PMF) (n : Nat) (a : Bool) : PMF :=
  match n with
  | Nat.zero => bottom
  | succ n => WhileFunctional cond body (prob_while_cut cond body n) a

def test_cond (b : Bool) : Bool := ¬ b
def test_body (_ : Bool) : PMF := λ b => if b = true then 0.5 else 0.5

def loop (n : Nat) : PMF := prob_while_cut test_cond test_body n false

#eval loop 0
#eval loop 1
#eval loop 2
#eval loop 3
#eval loop 4
#eval loop 5

def loop2 (n : Nat) : PMF :=
  bind (test_body false) (prob_while_cut test_cond test_body n)

#eval loop2 0
#eval loop2 1
#eval loop2 2
#eval loop2 3
#eval loop2 4
#eval loop2 5
