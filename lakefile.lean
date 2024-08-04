import Lake
open Lake DSL

package «arith» where
  -- add package configuration options here

lean_lib «Arith» where
  -- add library configuration options here

@[default_target]
lean_exe «arith» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"
