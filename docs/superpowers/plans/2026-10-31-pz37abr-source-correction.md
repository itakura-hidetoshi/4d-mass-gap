# PZ37ABR original-source correction implementation plan

> Execute inline; GitHub MCP only for repository operations. No git/gh CLI.

**Goal:** Derive the original kernel section, without an inserted Perron factor, from its actual four-edge marginal and connect it to ABQ2 by the exact correction S/R.

**Architecture:** Add an abstract finite-product weighted-kernel integration lemma, then specialize to the unchanged Wilson half-weights, actual complement and kernel. Keep S (no source-side vacuum) distinct from R (ABQ2, with vacuum). Normalize by the actual ABQ2 mass, not a temporal Haar power.

**Tech stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User handoff dated 2026-10-31 and continuation instruction. Base exact HEAD 44949d410ecf4e941c2f3fcd0208510ca640dc85.

## Global constraints
- Authoritative branch formal/real-hilbert-uniform-coercive-strong-limit; main is only a documentation mirror.
- Add new files only; do not change original definitions, existing proofs, dependency pins or workflows.
- No sorry, admit, new axiom or native_decide.
- Use the actual complement and the same DecidableEq Link, Fin 2 Fintype and original measurable-space implementation as ABQ2.
- All claimed proof completion requires completed exact-source CI, changed-file warning/error 0/0, standard axioms and independent completion receipt.

## Review focus
- Both finite product implicit instances and opaque Measure.pi must agree.
- Signed integrals require actual integrability; no positivity conclusion from the total-integral convention.
- S is not R and V=S/R is not set to one.
- Actual t*Omega(B) is not replaced by Z_b^|Link|.
- No GI lower floor, negative-tail bound, Hilbert coercivity or continuum statement is inferred.

## Tasks
- [ ] Generic weighted finite-product kernel Fubini; compact-parameter continuity by dominated convergence.
- [ ] Physical S integrability, continuity and strict positivity; R continuity; exact original kernel section without source vacuum.
- [ ] V positive and R*V=S; normalized true Perron four-edge density of mass one; original-source corrected formula and signed positive/negative split.
- [ ] Open isolated-branch PR and inspect exact-source CI; repair only after reading the full files and dependencies; merge only if all gates complete.

## Validation ledger
No local lean/lake executable is installed. Kernel checks must be run by the existing GitHub Actions workflow. Local static tests are not Lean proof verification.
Prior conversational claim of four files/23 theorems has no recoverable saved implementation; it is not used as evidence.
