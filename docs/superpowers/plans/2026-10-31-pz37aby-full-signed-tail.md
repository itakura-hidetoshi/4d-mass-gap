# P4-Q2-PZ37ABY Full Signed Tail Implementation Plan

**Goal:** Control the entire original negative contribution by the actual physical receiver / temporal Wilson crossing mismatch, without assuming a tail cap N.
**Authority:** formal/real-hilbert-uniform-coercive-strong-limit, verified parent 72ea17713148f75bc59be714e0211a8b710e5a6d (ABX #6036).
**Tech:** Lean v4.30.0-rc2, mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6. GitHub MCP only for writes; no git/gh CLI.
**Design:** Prefer an unconditional two-sided whole-tail comparison over a new conditional restatement of ABX or an assumption of fixed-cap alignment. Derive D=k*c from the actual two posterior rows; exp(-32b)<=k<=exp(32b), including c=0. This scalar k is not a posterior and its diagonal convention makes no continuity claim. Use the same original FF response to define Psi_s=s*(F(g)-F(h))*c. Both signs are retained throughout integration.

- [ ] Add determinant upper bound via the reversed crossing and exp(-c)>=1-c; prove the exact slope and matching two-sided absolute bounds.
- [ ] Add the exact physical cross pair, its continuity/integrability and actual energy representation c=2b(Eh-Eg).
- [ ] Prove pointwise negative-set identity and two-sided full positive/negative moment bounds; no mass or sign region is discarded.
- [ ] Combine with ABT's exact GI formula and ABX's derived rectangle, keeping the actual mismatch integral explicit.
- [ ] Check full new source, imported theorem signatures and pinned APIs. Kernel CI must complete at exact source with all 16 public axiom reports standard-only, no sorryAx and changed diagnostics 0/0; require separate completion receipt before squash.
- [ ] Synchronize README/ROADMAP for ABX and verified ABY, then main as docs-only mirror, preserving existing bytes and avoiding redundant Lean CI.

**Review edges:** b=0, c=0, both crossing orientations, arbitrary signed source, s=-1 and s=0, all finite H including H=0. No division by b. No original definition, hypothesis, transfer normalization, Perron representative, posterior, public root or dependency pin changes.
**OPEN:** This comparison does not prove mismatch small relative to the aligned contribution, a volume-uniform rectangle Haar mass/amplitude, all-Hilbert coercivity, a common fine interval, OS/Wightman, or continuum mass gap. ABX's region need not be ABV's fixed cap; do not transplant the 1/64 bound. All historical signed cancellation obstructions remain in force.
