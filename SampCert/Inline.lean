import Lean
import SampCert.Extension

namespace Lean.ToDafny

syntax (name := inline_RandomM) "inline_RandomM" : attr

initialize
  registerBuiltinAttribute {
    ref   := by exact decl_name%
    name  := `inline_RandomM
    descr := "instruct Lean to inline a RandomM computation during extraction."
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName _ _attrKind => do
     modifyEnv fun env => extension.addEntry env (.addInline declName)
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

end Lean.ToDafny
