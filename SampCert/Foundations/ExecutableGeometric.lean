/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

open Nat

def State : Type := Bool × Nat
  deriving DecidableEq

def bound : Nat := 6

instance : Repr State where
  reprPrec := λ st : State => λ _ => s!"({st.1},{st.2})"

def PMF := State → Float

def myprint (bound : Nat) (p : PMF) : String :=
  s!"(true,{bound}) -> {p (true,bound)}, (false,{bound}) -> {p (false,bound)} \n "
    ++ if bound = 0 then "" else myprint (bound - 1) p

instance : Repr PMF where
  reprPrec := λ p : PMF => λ _ => myprint bound p

def pure (a : State) : PMF :=
  fun a' => if a' = a then 1 else 0

def mysum (p : PMF) (f : State → PMF) (b : State)  (bound : Nat) : Float :=
  p (true,bound) * f (true,bound) b + p (false,bound) * f (false,bound) b
  + if bound = 0 then 0 else mysum p f b (bound - 1)

def bind (p : PMF) (f : State → PMF) : PMF :=
  fun b => mysum p f b bound

def bottom : PMF := λ _ => 0

def WhileFunctional (cond : State → Bool) (body : State → PMF) (wh : State → PMF) : State → PMF :=
  λ a : State =>
  if cond a
  then bind (body a) (λ v => wh v)
  else pure a

def prob_while_cut (cond : State → Bool) (body : State → PMF) (n : Nat) (a : State) : PMF :=
  match n with
  | Nat.zero => bottom
  | succ n => WhileFunctional cond body (prob_while_cut cond body n) a

def test_cond (n : Bool × Nat) : Bool := n.1
def test_body (st : Bool × Nat) : PMF := λ b => if b.1 = true && b.2 = st.2 + 1 then 0.5 else if b.1 = false && b.2 = st.2 + 1 then 0.5 else 0

def loop (n : Nat) : PMF := prob_while_cut test_cond test_body n (true,0)

#eval loop 0 -- off by one because of fuel
#eval loop 1
#eval loop 2
#eval loop 3
#eval loop 4
#eval loop 5
#eval loop 6
