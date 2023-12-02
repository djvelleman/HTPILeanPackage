import Lake
open Lake DSL

package htpi {
  moreServerArgs := #[
    "-Dlinter.unusedVariables=false", -- ignores unused variables
    "-Dpp.funBinderTypes=true"  -- shows types of bound variables
  ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

@[default_target]
lean_lib HTPILib {
  moreLeanArgs := #[
    "-Dlinter.unusedVariables=false", -- ignores unused variables
    "-Dpp.funBinderTypes=true"  -- shows types of bound variables
  ]
}
