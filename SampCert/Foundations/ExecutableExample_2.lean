/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

open Nat

def PMF := Nat → Float

instance : Repr PMF where
  reprPrec := λ p : PMF => λ _ => s!"[0 -> {p 0} , 1 -> {p 1}, 2 -> {p 2}]"

def pure (a : Nat) : PMF :=
  fun a' => if a' = a then 1 else 0

def bind (p : PMF) (f : Nat → PMF) : PMF :=
  fun b => p 0 * f 0 b + p 1 * f 1 b + p 2 * f 2 b

def bottom : PMF := λ _ => 0

def WhileFunctional (cond : Nat → Bool) (body : Nat → PMF) (wh : Nat → PMF) : Nat → PMF :=
  λ a : Nat =>
  if cond a
  then bind (body a) (λ v => wh v)
  else pure a

def prob_while_cut (cond : Nat → Bool) (body : Nat → PMF) (n : Nat) (a : Nat) : PMF :=
  match n with
  | Nat.zero => bottom
  | succ n => WhileFunctional cond body (prob_while_cut cond body n) a

def test_cond (n : Nat) : Bool := n = 1
def test_body (_ : Nat) : PMF := λ n => if n = 0 then 0.1 else if n = 1 then 0.7 else if n = 2 then 0.2 else 0.0

def loop (n : Nat) : PMF := prob_while_cut test_cond test_body n 1

#eval loop 0
#eval loop 1
#eval loop 2
#eval loop 3
#eval loop 4
#eval loop 5
#eval loop 6
#eval loop 7
#eval loop 8
#eval loop 9
#eval loop 10
#eval loop 100

#eval 0.2
#eval 0.2 + 0.2 * 0.7
#eval 0.2 + 0.2 * 0.7 + 0.2 * 0.7^2
#eval 0.2 + 0.2 * 0.7 + 0.2 * 0.7^2 + 0.2 * 0.7^3

#eval 0.2 / 0.3

def loop2 (n : Nat) : PMF :=
  bind (test_body 1) (prob_while_cut test_cond test_body n)

#eval loop2 0
#eval loop2 1
#eval loop2 2
#eval loop2 3
#eval loop2 4
#eval loop2 5
