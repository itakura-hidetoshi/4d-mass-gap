# P4-Q2-PZ37AMY — original interacting finite Wilson positive-half temporal-gauge cylinder remains nonzero

Date: 2026-11-17 JST. Authoritative branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` docs mirror separately tracked. Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only / tighten-only / overwrite-forbidden / same-root.

## Exact original-model scope

AMW #6830 proves a genuinely nonzero two-Wilson-mode state in the original normalized SU(2) physical one-slab full top-orthogonal Gauss-law sector and its explicit continuous native spatial plaquette cylinder representative. AMX #6833 transports that SAME literal cylinder to strict positive time one of the native half-cylinder **product spatial Haar path** and proves nonvanishing; that by itself is not the interacting Wilson path measure.

AMY applies the exact **original** temporal-gauge finite positive-half Wilson path kernel (product of the genuine (H+1) one-slab Wilson weights) as `ENNReal.ofReal` density of that same Haar path measure. No original plaquette/Haar/Gauss/Wilson action/AJA/beta0/normalization/OS semigroup definition is replaced.

Five new Lean theorems in additive `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PositiveHalfTemporalGaugeWeightedCylinderV5_PZ37AMY.lean` (175 lines, source blob `4ef47abd3eab5599fa4956e08e07184af0a01e0c`):
1. `p4Q2PZ37AMY_originalTemporalGaugePathDensity_measurable`: original Wilson path density measurable.
2. `p4Q2PZ37AMY_originalTemporalGaugePathDensity_ne_zero`: strict Boltzmann positivity gives pointwise nonzero density for every path and real beta.
3. `p4Q2PZ37AMY_originalPathHaar_ac_weightedWilson`: original path Haar is absolutely continuous relative to genuine *unnormalized* interacting Wilson-weighted half-path measure.
4. `p4Q2PZ37AMY_weightedWilson_ac_originalPathHaar`: reverse absolute continuity, preserving the exact null sets.
5. `p4Q2PZ37AMY_exists_nonzero_weighted_originalWilsonTimeOneCylinder`: the concrete AMW physical top-orthogonal two-mode time-one Wilson cylinder is not a.e. zero under this actual interacting finite temporal-gauge half-path weight.

## Exact-source machine certification

- Original theorem [PR #6836](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6836) **MERGED**.
- Exact-source HEAD `164545b24fd10fcddca3fbb1d9b002fd6c3f691e`.
- [Exact-source CI #44021985887](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44021985887): event `pull_request`, completed/SUCCESS. Mandatory Lean job `133833364264` and mandatory Lean fast-check step completed/SUCCESS.
- Actual decoded Lean log: **Build completed successfully (8839 jobs)**. All five `#print axioms` outputs contain only `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` absent; AMY source direct warning/error **0/0**.
- Independent source receipt job `133834846253` completed/SUCCESS: `[mcp-receipt] event=pull_request exact_sha=164545b24fd10fcddca3fbb1d9b002fd6c3f691e source_result=success run=44021985887 attempt=1`.
- Source tree, test-merge tree, and canonical Formal integration tree: **`44666734b66afe7fa2b8fc6322c9cc933a770c83`**.
- Formal theorem merge HEAD **`6f8368e7d9b03d1e23f03c5c28544fbad36faf56`**.

## Independently verified canonical push certification

- [Independent Formal push CI #44026651063](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44026651063): event `push`, exact head `6f8368e7d9b03d1e23f03c5c28544fbad36faf56`, attempt 1, completed/SUCCESS. Required Lean job `133848489219` / mandatory Lean step completed/SUCCESS; decoded log **8839/8839**; five AMY axiom outputs standard-three only, no `sorryAx`, source-direct warnings/errors 0/0.
- Independent receipt job `133849553282` completed/SUCCESS: `[mcp-receipt] event=push exact_sha=6f8368e7d9b03d1e23f03c5c28544fbad36faf56 source_result=success run=44026651063 attempt=1`.

## Exact boundary of the result

AMY's weighted path measure is the **unnormalized** original finite Wilson temporal-gauge positive-half path. Positivity and mutual absolute continuity do not make it automatically the **full-periodic** interacting Wilson Gibbs probability, nor an element of the arbitrary abstract OS `D.positiveTimeSubalgebra`. Neither `C.translate` nor the canonical OS boundary reconstruction is identified with the genuine normalized physical one-slab. No continuum four-dimensional Yang–Mills mass gap is proved.

A distinct next stage AMZ is intended to prove the actual half-path partition mass positive and finite and normalize this **same** interacting temporal-gauge half-path law, rather than silently assuming unit mass.

This record is docs-only; Strict Lean must not run.
