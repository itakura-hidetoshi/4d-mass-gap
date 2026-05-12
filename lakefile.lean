import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

package «MGAP4D» where
  srcDir := "."
  moreLeanArgs := #["-DautoImplicit=false"]

lean_lib «MGAP4D» where
  roots := #[`MGAP4D]
