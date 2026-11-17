# P4-Q2-PZ37AMZ — normalized genuine finite Wilson positive-half path law and nonzero time-one cylinder

Date: 2026-11-17 JST. Authoritative branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` is only a separately managed documentation mirror. Fixed Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; append-only/tighten-only/overwrite-forbidden/same-root.

## Original model; theorem boundaries

AMW and AMX construct a nonzero actual physical SU(2) Gauss-law top-orthogonal two-mode Wilson cylinder at strict positive half-path time 1 in the original **product-Haar** path L². AMY independently proves that the same *pointwise* cylinder is not a.e. zero for the original finite interacting **unnormalized** temporal-gauge positive-half Wilson path `ρ.withDensity w`, where `w` is the exact already existing positive Wilson path kernel.

AMZ works with this **same original finite lattice, same H+1-slabs, same time-one index, same SU(2) Wilson weight**. It uses the existing exact physical kernel bound `0<w≤1` for beta≥0 and the pre-existing generic `doobWeightMass` / `doobWeightedMeasure` normalization theorems. It introduces no original Haar, Wilson, Gauss, beta0, AJA, normalized physical one-slab, OS semigroup or source-root change.

New Lean file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2NormalizedPositiveHalfTemporalGaugeCylinderV5_PZ37AMZ.lean`, 228 source lines; exact source SHA `82fd84e3df3116e2f2acdca70cb4ae22da125c19`; blob `5865578ad6c92eec0107cf5fec8af16766ccfbf9`.

## Eight separately audited theorems

1. `p4Q2PZ37AMZ_originalPathDensity_le_one`: original exact Wilson ENNReal path density satisfies `w≤1` for all path at beta≥0.
2. `p4Q2PZ37AMZ_originalHalfPathPartitionMass_le_one`: genuine original half-path partition mass `Z_half=∫⁻w dρ≤1`.
3. `p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_zero`: `Z_half≠0`, proved using AMY's actual absolute continuity `ρ≪ρ.withDensity w` and `ρ(univ)=1`, not a positivity assumption.
4. `p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_top`: `Z_half≠∞`.
5. `p4Q2PZ37AMZ_originalWeightedPath_isFiniteMeasure`: original unnormalized interacting Wilson half-path law has finite mass.
6. `p4Q2PZ37AMZ_originalNormalizedHalfPath_isProbabilityMeasure`: precisely normalized same Wilson half-path `doobWeightedMeasure ρ w` is probability, total mass 1.
7. `p4Q2PZ37AMZ_originalPathHaar_ac_normalizedWilson`: the original independent spatial Haar path `ρ` is absolutely continuous with respect to this **normalized interacting finite half-path probability**; the exact positive density and finite normalizer are used.
8. `p4Q2PZ37AMZ_exists_nonzero_normalized_originalWilsonTimeOneCylinder`: the same two-mode physical Wilson top-orthogonal cylinder has an explicit pointwise representative which remains not a.e. zero under this normalized interacting half-path probability. AMY's nonzero weighted-cylinder theorem and actual measure comparisons supply the witness.

These are proofs about actual original finite temporal-gauge half-path path measures. They do **not** identify this normalized half-path law with the **original full-periodic interacting Wilson Gibbs probability**, nor lift the observable to arbitrary abstract `D.positiveTimeSubalgebra`, nor show a physical normalized one-slab equals the abstract `C.translate`.

## Machine source certification

- [Theorem PR #6837](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6837) **MERGED**.
- Exact-source HEAD `82fd84e3df3116e2f2acdca70cb4ae22da125c19`; [source CI #44027164098](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44027164098): event `pull_request`, workflow completed/SUCCESS.
- Mandatory Lean job `133850161969` and mandatory `Run changed Lean fast check` step completed/SUCCESS. Actual decoded log ends: **Build completed successfully (8841 jobs).**
- Eight new `#print axioms`: 8/8 contain exactly `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`. AMZ changed-source warning/error **0/0**.
- Independent source receipt job `133851182059` completed/SUCCESS: `[mcp-receipt] event=pull_request exact_sha=82fd84e3df3116e2f2acdca70cb4ae22da125c19 source_result=success run=44027164098 attempt=1`.
- Source Git tree, actual PR test-merge and merged Formal commit: `74ca8ce071cfb3b0ddd4f709645e99add73a303b` all identical.
- Canonical Formal theorem merge HEAD `7822a401f3d43ba45dbcb4706a15739a43789093`.

## Canonical postmerge push — distinct pending observation

- Independent Formal push CI [#44027602975](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44027602975), exact `head_sha=7822a401f3d43ba45dbcb4706a15739a43789093`, event `push`, was `in_progress` at drafting.
- **Do not** record canonical independent push SUCCESS until workflow, required Lean step, logs, axiom audit, and exact SHA receipt all complete. Append an independent later checkpoint rather than overwriting this pending entry.

## Further unproved seams

Even this normalized genuine temporal-gauge positive-half law remains a finite half-path model, not an automatically identified periodic Gibbs marginal nor a compatible positive-time OS state for a given coherent `Q`. An actual Gibbs spatial-temporal restriction identity (with gauge fixing/reflection/orientation/wraparound) and a typed OS boundary carrier are separately needed, followed by one-slab operator comparison and continuum scaling. Nothing here proves a 4D continuum Yang–Mills mass gap.

Docs-only: no Strict Lean run requested.

## 2026-11-17 JST append-only canonical push SUCCESS reobservation

The earlier `in_progress` checkpoint above remains a correct historical observation; this later independent GitHub MCP reobservation establishes completion **on the exact integrated AMZ Formal HEAD**.

- [Independent canonical push workflow #44027602975](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44027602975): `event=push`, exact `head_sha=7822a401f3d43ba45dbcb4706a15739a43789093`, attempt 1, workflow **completed/SUCCESS**.
- Mandatory Lean job `133851581569` and `Run changed Lean fast check` step completed/SUCCESS. Decoded log ends `Build completed successfully (8841 jobs).`.
- All eight AMZ theorem `#print axioms` outputs contain exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, changed-source warning/error `0/0`.
- Independent receipt job `133852561466` completed/SUCCESS, actual log: `[mcp-receipt] event=push exact_sha=7822a401f3d43ba45dbcb4706a15739a43789093 source_result=success run=44027602975 attempt=1`.
- The AMZ theorem source is now **FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED** in precisely its original finite temporal-gauge normalized half-path scope. The original fully periodic Gibbs/OS one-slab identification and continuum 4D mass gap remain open.

This is docs-only; no Strict Lean rerun is required.
