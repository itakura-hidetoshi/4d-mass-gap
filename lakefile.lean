import Lake
open Lake DSL

package «MGAP4D» where
  srcDir := "."
  moreLeanArgs := #["-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_lib «MGAP4D» where
  roots := #[`MGAP4D]
