from ctypes import *

# Loading Lean's libraries
CDLL("/Users/trjohnb/.elan/toolchains/leanprover--lean4---v4.10.0-rc2/lib/lean/libInit_shared.dylib", RTLD_GLOBAL)
lean = CDLL("/Users/trjohnb/.elan/toolchains/leanprover--lean4---v4.10.0-rc2/lib/lean/libleanshared.dylib", RTLD_GLOBAL)

# import-graph uses some Lake definitions that are available in the lake library, but 
# Lean does not produce a dynamic version
# One needs to create the library
# On Mac, it looks like: #clang++ -fpic -shared -Wl,-force_load libLake.a -o libLake_shared.dylib -L . -lleanshared
# If you are in the lib/lean directory of your toolchain
CDLL("/Users/trjohnb/.elan/toolchains/leanprover--lean4---v4.10.0-rc2/lib/lean/libLake_shared.dylib", RTLD_GLOBAL)

# Loading Mathlic and its dependencies
# To create the dynamic library, for each one of them, run lake build xxx:shared
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/build/lib/libleanffi.dylib", RTLD_GLOBAL) 
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/cli/.lake/build/lib/libCli.dylib", RTLD_GLOBAL)
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/batteries/.lake/build/lib/libBatteries.dylib", RTLD_GLOBAL)
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/aesop/.lake/build/lib/libAesop.dylib", RTLD_GLOBAL)
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/proofwidgets/.lake/build/lib/libProofWidgets.dylib", RTLD_GLOBAL)
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/qq/.lake/build/lib/libQq.dylib", RTLD_GLOBAL)
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/importGraph/.lake/build/lib/libImportGraph.dylib", RTLD_GLOBAL)

# Loading SampCert's FFI
CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/packages/mathlib/.lake/build/lib/libMathlib.dylib", RTLD_GLOBAL)

# Loading SampCert
samplers = CDLL("/Users/trjohnb/Code/Lean/SampCert/.lake/build/lib/libSamplers.dylib", RTLD_GLOBAL) 

# Initialization
lean.lean_initialize_runtime_module()
lean.lean_initialize()

builtin = c_uint8(1)
# Because of static inlines in lean.h, we have to unfold everything
lean_io_mk_world = c_uint64(1)

res = samplers.initialize_Samplers(builtin, lean_io_mk_world)

lean.lean_io_mark_end_initialization()

# Initialization complete

r1 = samplers.my_test(c_uint32(42))

print(r1)

samplers.dgs_print(c_uint32(40),c_uint32(1))

r2 = samplers.dgs_get(c_uint32(40),c_uint32(1))

print(r2)