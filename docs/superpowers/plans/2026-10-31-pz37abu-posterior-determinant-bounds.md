# PZ37ABU Genuine Posterior Determinant Bounds Implementation Plan

> Execute inline with GitHub MCP. No git/gh CLI; isolated new branch.

**Goal:** Connect ABT's actual two-posterior determinant to the exact Wilson temporal crossing and a volume-independent positive amplitude floor.

**Architecture:** One generic positive-real determinant/log-cross identity; one physical leaf specializing the unchanged ABT densities with FR's original normalized log crossing and FK's genuine density bounds. Keep the physical response separate and state alignment only as an explicit conditional premise.

**Tech Stack:** Lean v4.30.0-rc2; mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User's continuation of ABT #6028, merged at authoritative dd5409990c522ec7dc86e2042e469521d8d718bc. Read ABT, FK and FR full sources; read fixed mathlib Real.add_one_le_exp.

## Design
For actual densities p0,p1, define D=p0(g)p1(h)-p1(g)p0(h). Prove D=p1(g)p0(h)(exp(c)-1), where c is the Wilson temporal energy crossing, independent of the finite volume, selected link and background. FK gives exp(-32b)<=p1(g)p0(h)<=exp(32b). Thus c>=0 implies D>=exp(-32b)c. Swap gives |D|>=exp(-32b)|c|. At g=1,h=R(pi), c=4b. The signed physical pair has a corresponding lower bound only when both response and crossing have the explicitly required sign.

## Global Constraints
- Sole theorem authority: formal/real-hilbert-uniform-coercive-strong-limit; main is a documentation mirror.
- Add leaf files only. No changes to old theorems, physics, physical transfer norm, pins, roots or CI workflows.
- No sorry, admit, new axiom or native_decide. No lowered hypotheses.
- No positive GI margin, full negative-tail bound, outer pair-Haar floor, Hilbert coercivity or continuum claim inferred from density-only positivity.
- CI gate requires completed exact-source run/job/Lean step, changed-file warning/error 0/0, standard axiom dependencies, no sorryAx and separate completion receipt.

## Review Focus
- All finite H including zero, every link and right environment; b=0 allowed in non-strict bounds.
- Both densities are the original interacting normalized laws, not Haar substitutes.
- Explicit H dependence and explicit Measure.prod at any product measure use.
- Mixed logarithm order and determinant orientation must agree; swapping negates both.
- Actual physical receiver is not replaced by a convenient function.

## Tasks
- [ ] Generic positive-real cross logarithm identity.
- [ ] H-independent temporal crossing and its 1/pi value; original density bounds and normalized-log bridge.
- [ ] Exact determinant, product amplitude bounds, sign equivalence, linear and absolute lower estimates.
- [ ] Conditional signed physical pair bound; static contract and numerical sanity checks.
- [ ] Exact-source CI, full-source repair if needed, axiom and completion checks, merge only after all gates.

## Verification ledger
Local lean/lake are not installed. Static declaration contract RED observed before implementation (missing new leaf), then GREEN on 14 theorem/axiom-print pairs. 250 scalar numerical cross-log and absolute-floor sanity checks passed; these are not kernel proofs. GitHub blob hashes match locally reviewed source bytes. No independent reviewer tool is available; review is inline and is not represented as independent expert review.
