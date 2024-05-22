/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Lean
import SampCert.Extractor.IR

namespace Lean.ToDafny

structure State where
  map : SMap Name String := {}
  decls : List String := []
  inlines : List String := []
  glob : SMap String MDef := {}
  deriving Inhabited

def State.switch (s : State) : State :=
  { s with map := s.map.switch }

inductive Entry where
  | addDecl (declNameLean : Name) (declNameDafny : String)
  | toExport (dafnyDecl : String)
  | addInline (declNameLean : Name)
  | addFunc (defnName : String) (defn : MDef)
  deriving Inhabited

def addEntry (s : State) (e : Entry) : State :=
  match e with
  | .addDecl key val => { s with map := s.map.insert key val }
  | .toExport decl => { s with decls := decl.replace "SLang." "" :: s.decls }
  | .addInline name => { s with inlines := name.toString :: s.inlines }
  | .addFunc key val => { s with glob := s.glob.insert key val}

initialize extension : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries addEntry {} es).switch
  }

end Lean.ToDafny
