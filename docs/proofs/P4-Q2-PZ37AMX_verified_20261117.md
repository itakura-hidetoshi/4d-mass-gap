# P4-Q2-PZ37AMX — original first-positive-time SU(2) Wilson-cylinder on the genuine positive-half path Haar carrier

Date: 2026-11-17 JST. Authoritative branch `formal/real-hilbert-uniform-coercive-strong-limit`; Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only, tighten-only, overwrite-forbidden, same-root. No original Wilson action, beta0, AJA, lattice, Haar, Gauss law or OS semigroup modification.

## Actual theorem scope

The independently source/push-certified AMW stage constructs a nonzero physical SU(2) Gauss-law state in the full normalized Wilson one-slab top eigenspace orthogonal complement as a two-mode finite Wilson plaquette Gram–Schmidt combination; it also identifies the precise time-zero Haar-a.e. Wilson-cylinder observable.

AMX builds a *different, genuinely time-positive* witness on the original finite even-periodic positive-half-cylinder spatial path:

- `p4Q2PZ37AMX_positiveTimeOne`: actual strict time-one index in `Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1)` for all `H`, including `H=0`.
- `p4Q2PZ37AMX_positiveTimeOne_measurePreserving`: the original positive-half spatial path independent product-Haar measure pushed forward by time-one slice evaluation is exactly the unchanged native spatial-slice Haar probability. This uses pinned Mathlib `measurePreserving_eval`; no model-specific measure substitution.
- `p4Q2PZ37AMX_positiveTimeOneL2Pullback`: canonical real `Lp.compMeasurePreservingₗᵢ` linear isometry from the true spatial-slice Haar `L²` into the original positive-half spatial-path Haar `L²`.
- `p4Q2PZ37AMX_exists_nonzero_oneStepPositiveHalfWilsonCylinder`: the actual AMW physical Gauss-law/top-orthogonal two-mode state has a *nonzero* time-one positive-half path `L²` lift, with an explicit a.e. representative equal to the two continuous original SU(2) Wilson-energy Gram–Schmidt class functions evaluated on the actual time-one primary spatial plaquette cyclic holonomy.

One additive source `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PositiveTimeOneFiniteCylinderHaarV5_PZ37AMX.lean`, final 169 lines, exactly two theorem `#print axioms` audits; the time-one index and isometry are also compiled definitions.

## Historical exact-source failure and repair, kept append-only

- First candidate HEAD `daa6ea6a29d2e3637b6c3dfe89b473c275e23531`, [CI #44019751571](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44019751571) completed/FAILURE. Five direct errors all requested `MeasurableSpace` for the original SU(2) spatial configuration or positive-half spatial path: local measurable SU(2) instance was missing, because imported modules' `local instance` declarations are not inherited into the new elaboration context. Downstream `sorryAx` from ill-typed declarations was **not** accepted as an axiom certificate.
- Source-local repair: install the exact standard pinned SU(2) `IsTopologicalGroup`, `CompactSpace`, `SecondCountableTopology`, `MeasurableSpace`, `BorelSpace` local instances already used by the original positive-half Haar modules. No theorem statement, hypothesis, physical model, imported authoritative content or normalization changed.
- Corrected exact-source HEAD `fc65eb9dee3eea2e6a81629cf7572ccb3dbffb50`.

## Independently certified source and Formal integration

- [Theorem PR #6833](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6833) MERGED.
- [Exact-source PR CI #44020168605](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44020168605): event `pull_request`, exact source HEAD `fc65eb9dee3eea2e6a81629cf7572ccb3dbffb50`, workflow completed/SUCCESS, mandatory Lean job `133827497760`, required `Run changed Lean fast check` step completed/SUCCESS.
- Actual decoded log: `Build completed successfully (8833 jobs).`, two explicit theorem axiom prints contain only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; AMX direct warning/error `0/0`.
- Exact-source completion receipt job `133828357451` completed/SUCCESS: `[mcp-receipt] event=pull_request exact_sha=fc65eb9dee3eea2e6a81629cf7572ccb3dbffb50 source_result=success run=44020168605 attempt=1`.
- Original source, actual PR test-merge, canonical Formal merge Git tree all **`aa4b58102b3855c2f452f517d97176511951a3ec`**.
- Formal theorem merge HEAD **`c5a9b78e74df562b143e33c7faa22c29f0e66b91`**.

## Independent canonical push: historical initial pending checkpoint

- [Independent push CI #44020541396](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44020541396) event `push`, exact `head_sha=c5a9b78e74df562b143e33c7faa22c29f0e66b91`. Initially `in_progress`. Append the exact completed workflow, mandatory Lean step and receipt later. An unfinished run is **not** a certificate.

## Precise open obstructions

1. Product path Haar `L²` is **not** the original interacting Wilson Gibbs probability. No false measure identification.
2. An explicit time-one Wilson cylinder as a measurable function on the original path does **not** automatically construct an element of abstract `D.positiveTimeSubalgebra` or a typed preimage under `Q.positiveHalfPullback`.
3. Actual OS boundary synthesis, time calibration, reflection orientation and one-slab intertwining between `C.translate` and the original normalized physical Wilson transfer remain unproved.
4. No continuum 4D Yang–Mills mass gap is established by this finite positive-time cylinder.

Docs-only; **no Strict Lean**.
