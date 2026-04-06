import Lake
open Lake DSL System

package «sampcert» where
  testDriver := "test"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

-- From doc-gen4
meta if get_config? env = some "doc" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

target ffi.o (pkg : NPackage __name__) : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcFile ← inputFile (pkg.dir / "ffi.cpp") false
  let lean ← getLeanInstall
  buildO oFile srcFile
    (weakArgs := #[s!"-I{lean.includeDir}"])
    (traceArgs := #["-fPIC"])
    (compiler := "g++")

target libleanffi (pkg : NPackage __name__) : FilePath := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

target libleanffidyn (pkg : NPackage __name__) : Dynlib := do
  let ffiO ← ffi.o.fetch
  let libFile := pkg.sharedLibDir / nameToSharedLib "leanffi"
  let lean ← getLeanInstall
  let leanLibDir := lean.sysroot / "lib" / "lean"
  buildLeanSharedLib "leanffi" libFile #[ffiO] #[] (weakArgs := #[s!"-Wl,-rpath,{leanLibDir}"])

@[default_target]
lean_lib «SampCert» where
  extraDepTargets := #[`libleanffi, `libleanffidyn]

lean_lib «FastExtract»

lean_lib «VMC»

lean_exe test where
  root := `Test
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]

lean_exe check where
  root := `SampCertCheck
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]

/-
-- Old lakefile (pre-4.28 upgrade), kept for reference:
--
-- import Lake
-- open Lake DSL
--
-- package «sampcert» where
--   -- add any package configuration options here
--
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"
--
-- @[default_target]
-- lean_lib «SampCert» where
--   extraDepTargets := #[`libleanffi,`libleanffidyn]
--
-- lean_lib «FastExtract» where
--
-- lean_lib «VMC» where
--
-- -- From doc-gen4
-- meta if get_config? env = some "doc" then
-- require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
--
-- target ffi.o pkg : FilePath := do
--   let oFile := pkg.buildDir / "ffi.o"
--   let srcJob ← inputTextFile <| pkg.dir / "ffi.cpp"
--   let weakArgs := #["-I", (← getLeanIncludeDir).toString]
--   buildO oFile srcJob weakArgs #["-fPIC"] "g++" getLeanTrace
--
-- target libleanffi pkg : FilePath := do
--   let ffiO ← ffi.o.fetch
--   let name := nameToStaticLib "leanffi"
--   buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
--
-- target libleanffidyn pkg : FilePath := do
--   let ffiO ← ffi.o.fetch
--   let name := nameToSharedLib "leanffi"
--   buildLeanSharedLib (pkg.nativeLibDir / name) #[ffiO]
--
-- lean_exe test where
--   root := `Test
--   extraDepTargets := #[`libleanffi]
--   moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]
--
-- lean_exe check where
--   root := `SampCertCheck
--   extraDepTargets := #[`libleanffi]
--   moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]
--
-- lean_exe mk_all where
--   root := `mk_all
--   supportInterpreter := true
--   -- Executables which import `Lake` must set `-lLake`.
--   weakLinkArgs := #["-lLake"]
-/
