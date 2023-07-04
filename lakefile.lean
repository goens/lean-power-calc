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

require «egg-tactic» from git  "https://github.com/opencompl/egg-tactic-code" @ "9926446ba068f3ffd349c2c40aec7f1e82a8dc78"

@[default_target]
lean_exe «power-calc» {
  root := `Main
}
