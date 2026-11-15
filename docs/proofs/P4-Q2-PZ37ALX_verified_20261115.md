# P4-Q2-PZ37ALX — genuine original fixed-beta0 raw excited/full Wilson norm ratio

2026-11-15 JST. [Theorem PR #6764](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6764) **MERGED** on the authoritative `formal/real-hilbert-uniform-coercive-strong-limit` branch as `d9f5c4210a9afcf742ec5da573f83efc8dd7cf57`.

## Scope, original physical model, exact new equality

One new append-only Lean4 source leaf, 283 lines including the terminator and **15 independent `#print axioms` audits**:

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0RawSectorNormRatioV5_PZ37ALX.lean`

The original SU(2) one-slab physical Wilson operator `P_H: G_H→L[ℝ]G_H`, normalized full-top-orthogonal restriction `R_H: K_H→L[ℝ]K_H`, Haar/gauge/AJA definitions and the prescribed physical coupling `beta0=log(3/2)/64` are unchanged. The physical `K_H` is the original complete top-eigenspace orthogonal sector; there is no invented inter-volume Hilbert-space isomorphism.

ALX defines the **genuine raw restriction** `A_H=P_H.comp(K_H.subtypeL)` (a `K_H→L[ℝ]G_H` map). Its previously certified exact same-volume normalization transport and a separately proved generic operator-norm scaling lemma imply unconditionally:

```text
forall x in K_H: ||A_H x||=||P_H||*||R_H x||
||A_H||=||P_H||*||R_H||
||A_H||²=Q_H*||P_H||²,  Q_H=||R_H||².
```

This is a **true exact algebraic equality for the original physical finite-volume model**, not a Haar-moment lower-floor approximation. It removes the slack from ALW's `F_H <= ||P_H||`. The equality itself is not an independent finite-size gap estimate.

## Separately unproved two-volume comparison and conditional descent

ALX defines the true scalar *cross-volume* ratio criterion, comparing only real numbers, not the operators on their different Hilbert carriers:

```text
||A_(H+1)||² <= (Q_H+b_H)*||P_(H+1)||².
```

Because `||P_(H+1)||>0`, the exact ratio identity implies `Q_(H+1)<=Q_H+b_H`; for nonnegative b_H this gives ALU's actual downward loss `L_H<=b_H`. If **independently** `b_H>=0` and all finite partial sums satisfy `sum_{i<H}b_i<=B<delta_0`, ALU constructs a positive uniform fixed-beta0 finite-volume gap. Geometric `b_H=C*r^H` with `0<=r<1` and `C<(1-r)*delta_0` is another sufficient hypothesis; a tail-only version after any finite prefix M combines with ALT's unconditional positive prefix certificate.

**OPEN/NO_DATA:** No original Wilson two-volume ratio estimate, numerical upper bound on `b_H`, summable/geometric bound, original beta0 all-H gap, Hamiltonian gap or continuum 4D Yang–Mills mass gap has been established by ALX. The raw/full norm ratio criterion is exactly equivalent to the normalized `Q_(H+1)` scalar step bound: re-expression alone does NOT provide the missing genuine physical estimate. Independent physical Wilson local-kernel and normalizer analysis remains necessary.

## Lean4 elaboration repair and audit provenance

Pinned Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, unchanged existing imports, roots, operators, workflows and existing theorems.

Historical failed exact-source CI (retained, NOT reclassified as green):
- Initial source `22c2e105e7d5862938c56786e372feafc20209dd` / [#43660136067](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43660136067): FAIL.
- `089a7f22ca40330033d58026e46d6442fae62477` / [#43660856065](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43660856065): FAIL; local notation for physical CLM composition and typed raw/normalized transport revised.
- `fa07a0cf3e24c15236bb26e27729922687f4d3d1` / [#43661373703](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43661373703): FAIL; named physical top-orthogonal submodule's `NormedSpace` instance needed explicit exposure.
- `6f817734a371c16e2386ee4b9319f18c44f97366` / [#43661808195](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43661808195): FAIL; generic norm-scaling carrier arguments were explicitly pinned to `K_H,G_H`.
- `0a4033bdcd6e3ef8eb0de209224cdc22aec73015` / [#43662281766](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43662281766): FAIL; exact Lean line 150 still could not synthesize `NormedSpace ℝ K0`. Derived `sorryAx` outputs are FAILURE provenance, not certification.

Final fixed source `5c086f63023aed0bff2bb8f5d2ea1135daeaf3a6`, exact source blob `9615503c55d6dd5b5ede034cee1d5d1e5c366701`, supplies `Submodule.normedSpace K0` **explicitly** to the generic norm identity's class argument instead of relying on brittle implicit dependent typeclass synthesis. Theorem statements, physics and fixed pins are unchanged; no heartbeats increase or admitted proof.

[Exact-source PR CI #43663023266](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43663023266) **completed/SUCCESS**. Actual pinned Lean **11,488/11,488**; all **15/15** new `#print axioms` use only `propext`, `Classical.choice`, `Quot.sound`, no ALX `sorryAx`, changed ALX warning/error **0/0**. Main job `132656266763` completed SUCCESS, independent exact-head receipt job `132657616652` completed SUCCESS; actual receipt:

```text
[mcp-receipt] event=pull_request exact_sha=5c086f63023aed0bff2bb8f5d2ea1135daeaf3a6 source_result=success run=43663023266 attempt=1
```

Source, synthetic PR test merge and integrated squash have exactly matching Git tree `26cc3e880dbb4efdd29b0ae25de1e29a7649e236`.

The independent authoritative [push CI #43663546613](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43663546613) was **in progress at this initial record snapshot**. It must be reobserved independently, and a final completion receipt appended only after its actual workflow+job termination.

## Next research task

Establish a genuine original fixed-beta0 SU(2) Wilson physical **cross-volume** comparison of the raw sector norm `||A_H||` and full norm `||P_H||`. Such an estimate must be physically grounded by a validated lattice embedding/marginal-kernel construction or an independent two-scale scalar bound, and must control the *relative ratio* rather than bounding `||P_H||` alone. No all-H fixed-beta0 spectral or continuum mass gap follows solely from this theorem.


## Independent authoritative canonical push — completed receipt (2026-11-15 JST)

The independent push CI PENDING snapshot above was accurate at the time of writing. GitHub MCP has now separately verified [formal push CI #43663546613](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43663546613) **completed/SUCCESS**, **event=push**, at exact canonical authoritative theorem HEAD `d9f5c4210a9afcf742ec5da573f83efc8dd7cf57`.

Actual pinned Lean full dependency closure **11,488/11,488**, all **15/15** ALX `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`, zero ALX `sorryAx`, changed-file warning/error **0/0**. Main Lean job `132657882564` completed SUCCESS; independent exact-head completion receipt job `132659360957` completed SUCCESS. Receipt captured from actual job log:

```text
[mcp-receipt] event=push exact_sha=d9f5c4210a9afcf742ec5da573f83efc8dd7cf57 source_result=success run=43663546613 attempt=1
```

The same source/test-merge/canonical Git tree is `26cc3e880dbb4efdd29b0ae25de1e29a7649e236`. No new physical original fixed-beta0 two-volume norm-ratio estimate, uniform all-H gap or continuum Yang–Mills mass gap follows from this CI certification.
