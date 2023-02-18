import Lake
open Lake DSL

package «SSASlow»

lean_lib SSASlow

@[default_target]
lean_exe «ssa» {
  root := `SSASlow
  supportInterpreter := true
}

require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
