import Lake
open Lake DSL

package "remco-mul-div" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"
require "leanprover-community" / "aesop"

@[default_target]
lean_lib «RemcoMulDiv» where
  -- add any library configuration options here
