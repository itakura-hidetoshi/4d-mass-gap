# P4-Q2-PZ37ALS — independently certified original Wilson high-temperature concrete eight-color frame

2026-11-15 JST. **Authoritative theorem branch:** `formal/real-hilbert-uniform-coercive-strong-limit`.
Theorem [PR #6753](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6753) **MERGED**.
Original physical Wilson SU(2), its one-slab transfer, Haar, full top orthogonal carrier, exact fixed coupling `beta0=log(3/2)/64`, AJA and pinned Lean/mathlib are **unchanged**.

## Lean mathematics and scope

One added Lean4 file:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHighTemperatureConcreteEightColorFrameV5_PZ37ALS.lean` (386 source lines, 19 named declarations and 19 actual `#print axioms`).

On physical right-boundary lifts (with the true ground-state joint measure), existing twelve-spatial residual, true six spatial conditional expectations, and six spatial plus two identity temporal-color frame satisfy the exact carrier-safe identities:
```text
E12(JRight(U x)) = (1/2) E6(U x)
E8(P8,U x)       = (3/4) E6(U x) = (3/2) E12(JRight(U x))
```

On the **already-certified original high-temperature cutoff**, the existing volume-independent conventional twelve-spatial Poincaré coefficient `1/2304` yields the concrete eight-color frame coefficient `1/1536`, with NO new frame assumption at that scope. Combine with ALR's exact physical squared-defect-to-square-root inequality to derive, for all finite volumes in the stipulated interval,
```text
gap_H(beta) >= 1 - sqrt(1 - 1/1536) > 1/3072
```
and a positive physical coupling chosen before all H that differs from prescribed original `beta0`.

**Proven obstruction, not NO_DATA:** ALK establishes `betaStar < beta0` for the specific selected AKL cutoff. ALM additionally proves that **every** old high-temperature family cutoff with `s>8` is below `beta0`. ALS therefore does **not** prove an all-H gap at prescribed original `beta0`. The old conditional theorem with antecedent `beta0 <= betaStar` is a logical test with an antecedent ALK has already disproved, not a meaningful physical certificate.

## Full-source Lean repair and exact-source provenance

- Initial research HEAD `349755bda26ab2e18a80772672a6e6cfef5b46de`; [CI #43588165989](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43588165989) completed **FAILURE**. Whole new ALS source and ALR/ALK/AKL/12-spatial/6-spatial imports were read. There were **12 direct ALT-independent ALS diagnostics**: 11 unknown references to `p4Q2PZ37ADC_fixedCoupling` or `_pos` outside their actual `GroundStatePosteriorJoint` namespace (autoImplicit=false), plus one resulting `linarith` failure. Failed-head `sorryAx` in some printed audits was elaborator recovery, NOT certified.
- One source-only correction: qualify 11 original fixed-coupling references with `GroundStatePosteriorJoint.`, preserving the theorem statements, genuine Wilson physical source and all old declarations. Fixed head `8074fa960e15e26949062e941754c1533f49528b`.
- [Exact-source CI #43607964235](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43607964235) **completed/SUCCESS**; actual pinned Lean **11,483/11,483**. All **19/19** new ALS `#print axioms` emitted only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`; changed warnings/errors **0/0**, independent exact-head completion receipt **SUCCESS**.
- Canonical formal squash `d15e4f4d094beb036e9d5e36918ca1eb4503844c`. Source HEAD, PR synthetic test merge and authoritative squash all have the same actual Git tree `d01d426820ad8fa8c2089f9d241fe6c247bf4067`.
- [Independent canonical push CI #43608757057](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43608757057) **completed/SUCCESS**, **11,483/11,483**, all **19/19** ALS audits standard three, `sorryAx` absent, ALS warnings/errors 0/0, exact canonical HEAD completion receipt **SUCCESS**.

## Open mathematics

The cutoff does not contain the original prescribed `beta0`; a genuinely different model-specific Wilson bound is required. These finite original high-temperature transfer-gap theorems do **not** establish all-H original-fixed-`beta0` uniform gap, an OS Hamiltonian mass gap, or continuum 4D Yang–Mills mass gap. ALT and subsequent studies investigate the fixed-`beta0` side without weakening ALM's no-go.

Operating rules: append-only / tighten-only / overwrite-forbidden / same-root. Fixed Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
