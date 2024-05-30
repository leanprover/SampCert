/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

class MyAbstractLanguage (T : Type) where
  FOO : Type → Type
  plop : Monad FOO
  while_ :  (T → Bool) → (T → FOO T) → (init : T) → FOO T
