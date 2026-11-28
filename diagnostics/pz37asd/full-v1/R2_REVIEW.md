# ASD R2A — repair of terminal R1B diagnostics
Baseline and all 13 public audit targets unchanged.
R1B run 46137996716, job 140958175686: direct 9.740s, exit 1, MCP not started; all exact caches restored. Source blob 8641e854b18ded086dcfe708007103724edcd930. Preserve R1B, do not retry it.
Observed diagnostics: unused simp argument eq_comm (69); invalid simp theorem for local notation delta (84,92,196), downstream unsolved goals; wrong finrank_top namespace (215); unresolved Fintype Dir metavariable (252).
R2A removes the unused simp argument, explicitly unfolds the incidence and delta definitions, casts Nat addition and splits the endpoint indicators, uses pinned global finrank_top and CommSemiring.finrank_self, and computes the direction count by explicit equivalence with Fin 3. The zero-sum expansion uses the actual delta definition. No theorem statement changes, no linter suppression, no new assumptions.
Pinned API inspected in Mathlib/LinearAlgebra/Dimension/Finrank.lean and Mathlib/SetTheory/Cardinal/Finite.lean at 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Candidate only; direct Lean and actual MCP must pass before independent proof PR.
