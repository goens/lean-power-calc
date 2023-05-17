import Lake
open Lake DSL

package «power-calc» {
  -- add package configuration options here
}

lean_lib «PowerCalc» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "a5ac4ef"

require «egg-tactic» from git  "https://github.com/opencompl/egg-tactic-code" @ "8b4aa74"

@[default_target]
lean_exe «power-calc» {
  root := `Main
}
