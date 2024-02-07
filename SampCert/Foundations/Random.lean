/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic

open MeasurableSpace

attribute [simp] Lean.Internal.coeM
attribute [simp] Bind.bind
attribute [simp] Pure.pure
attribute [simp] CoeT.coe
attribute [simp] instCoeT
attribute [simp] CoeHTCT.coe
attribute [simp] instCoeHTCT_1
attribute [simp] CoeHTC.coe
attribute [simp] instCoeHTC_1
attribute [simp] CoeOTC.coe
attribute [simp] instCoeOTC_1
attribute [simp] CoeTC.coe
attribute [simp] instCoeTC_1
attribute [simp] Coe.coe
attribute [simp] optionCoe
attribute [simp] CoeOut.coe

variable {T : Type} [MeasurableSpace T]

abbrev RandomM (T : Type) := Pmf T
