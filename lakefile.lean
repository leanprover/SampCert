import Lake
open Lake DSL

package «sampcert» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0-rc2"

@[default_target]
lean_lib «SampCert» where
  extraDepTargets := #[`libleanffi,`libP2Sampler]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi", "-lP2Sampler"]

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
  discard <| buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
  buildLeanSharedLib (pkg.nativeLibDir / name) #[ffiO]

lean_lib P2Sampler where
  defaultFacets := #[LeanLib.sharedFacet, LeanLib.staticFacet, LeanLib.staticExportFacet]

target libP2Sampler : FilePath := do (← P2Sampler.get).static.fetch

lean_exe test where
  root := `Test
  extraDepTargets := #[`libP2Sampler,`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi", "-lP2Sampler"]

lean_exe more where
  root := `More
  extraDepTargets := #[`libP2Sampler,`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi", "-lP2Sampler"]
