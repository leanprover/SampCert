import Lake
open Lake DSL

package «sampcert» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

@[default_target]
lean_lib «SampCert» where
  extraDepTargets := #[`libleanffi,`libleanffidyn]

lean_lib «FastExtract» where

lean_lib «VMC» where

-- From doc-gen4
meta if get_config? env = some "doc" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "g++" getLeanTrace

target libleanffi pkg : FilePath := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

target libleanffidyn pkg : FilePath := do
  let ffiO ← ffi.o.fetch
  let name := nameToSharedLib "leanffi"
  buildLeanSharedLib (pkg.nativeLibDir / name) #[ffiO]

lean_exe test where
  root := `Test
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]

lean_exe check where
  root := `SampCertCheck
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]

lean_exe mk_all where
  root := `mk_all
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]
