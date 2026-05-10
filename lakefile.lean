import Lake
open Lake DSL

package «MGAP4D» where
  srcDir := "."
  moreLeanArgs := #["-DautoImplicit=false"]

lean_lib «MGAP4D» where
  roots := #[`MGAP4D]
