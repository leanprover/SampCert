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

theorem loop_0 : loop 0 = bottom := by
  unfold loop
  unfold prob_while_cut
  trivial

theorem loop_1 : loop 1 = bottom := by
  unfold loop
  unfold prob_while_cut
  unfold WhileFunctional
  unfold prob_while_cut
  unfold test_cond
  simp
  unfold test_body
  unfold _root_.bind
  simp -- b |-> 0.5 * (loop 0) b + 0.5 * (loop 0) b  (= xxx)
       -- 0.5 * (loop 0) true + 0.5 * (loop 0) true  ~> 0
  simp [bottom]
  sorry

def go2 : PMF := λ x => if x = True then 0.5 else 0.0

theorem loop_2 : loop 2 = go2 := by
  unfold loop
  unfold prob_while_cut
  unfold WhileFunctional
  unfold prob_while_cut
  unfold WhileFunctional
  unfold prob_while_cut
  unfold test_cond
  simp
  unfold test_body
  unfold _root_.bind
  unfold _root_.pure
  simp -- b |-> 0.5 * (if b then 1 else 0) + 0.5 * xxx (= yyy)
       -- 0.5 * (if true then 1 else 0) + 0.5 * xxx ~> 0.5 + 0
  sorry

def go3 : PMF := λ x => if x = True then 0.75 else 0.0

theorem loop_3 : loop 3 = go3 := by
  unfold loop
  unfold prob_while_cut
  unfold WhileFunctional
  unfold prob_while_cut
  unfold WhileFunctional
  unfold prob_while_cut
  unfold WhileFunctional
  unfold prob_while_cut
  unfold test_cond
  simp
  unfold test_body
  unfold _root_.bind
  unfold _root_.pure
  simp -- b |-> 0.5 * (if b then 1 else 0) + 0.5 * yyy
       -- 0.5 + 0.5 * 0.5 + 0 ~> 0.75
  sorry



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
#eval loop 11
