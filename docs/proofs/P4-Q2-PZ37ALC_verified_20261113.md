# P4-Q2-PZ37ALC — exact original SU(2) pair-Haar source moments

2026-11-13 JST. Authoritative formal branch `formal/real-hilbert-uniform-coercive-strong-limit`.
Source: [theorem PR #6731](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6731) **MERGED**.
Original complete Wilson SU(2), temporal crossing kernel, both spatial halfweights, centered physical ZW source, product Haar measure, normalized physical transfer, AJA budget and margin, full-top projector, coupling `beta0=log(3/2)/64`, original model H and dependency pins are unchanged.

## Genuine Lean4 content

Nine newly appended audited declarations in
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPairHaarQuadraticMomentV5_PZ37ALC.lean`:

1. Global exact scalar `1+x^2/4 <= (exp x + exp (-x))/2`.
2. Integrability of the original crossing-weighted signed two-boundary physical source.
3. **Vanishing original crossing-weighted first Haar moment**, descending the actual ALA product-Haar `MeasurePreserving` diagonal central transformation; not a formal parity assertion alone.
4. Definition of the actual original crossing-weighted second source moment `M2pair_H(beta)`.
5. Integrability of the true measured second moment.
6. `0 <= M2pair_H(beta)`; no numerical strictly positive lower bound is silently assumed.
7. **True non-Gaussian pair-Haar Laplace lower bound**
   `Zcross_H(beta) + (t^2/4)*M2pair_H(beta) <= Lpair_H(beta,t)`.
8. Immediate `Zcross_H(beta) <= Lpair_H(beta,t)`.
9. The same genuine second-moment lower bound specialized to **H=22**.

The quantitative correction uses the actual measured original pair-square under the original crossing kernel and normalized product Haar. It is not yet an exact physical one-slab norm improvement, a lower bound on `M2pair` by a positive H-dependent number, or a new physical model.

## Verified CI and corrective provenance

- Initial source `16caeaf8bc534bdf2c6d8dcad3bfd5ae687e7eb2`; [CI #43401508412](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43401508412) **FAILURE**, exactly one ALC direct Lean elaboration failure at line 187: syntactic `Pi.add_apply` not expanded before `ring` in an integrability equivalence. Subsequent three axiom prints showed `sorryAx`; this failed source is NOT certified.
- Fixed source `776207b858d37cfaf4920a4c39ebc00b5c5713ee`: explicit `dsimp only [Pi.add_apply]` before `ring`, no change to theorem statement, physical model or prior files.
- [Final exact-source CI #43402704562](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43402704562) **completed/SUCCESS**; actual `Run changed Lean fast check` completed/SUCCESS, pinned Lean v4.30.0-rc2, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Lean dependency closure **11,465/11,465**, all **9/9** new ALC `#print axioms` display **only** `propext`, `Classical.choice`, `Quot.sound`. No new `sorryAx`, changed ALC warnings/errors **0/0**.
- Canonical formal theorem squash `ee0843243261bfe239d6269f5a1dc2d6c3add2d8`. Source commit, PR test-merge and squash all have the **identical Git tree** `f0ed94feba23b15a1ae98387f7c27c332be93680`, independently fetched from exact Git commit objects.

### Independent formal push audit

[Canonical formal push CI #43403627674](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43403627674) started for exact formal HEAD `ee0843243261bfe239d6269f5a1dc2d6c3add2d8`. As of the initial record snapshot, completion and the independent exact-HEAD receipt are **PENDING / NO_DATA**. Retain this historical pending observation; append the actual final outcome only after the workflow, Lean job and independent completion receipt reach completed SUCCESS. Docs-only edits do not manually dispatch Strict Lean.

## Open physical obstruction and next proof work

AKZ certifies `r_H >= 1/2` for every H. At H=22 the unchanged AKX sufficient criterion requires the **actual** original negative-region Haar mass
`r22 <= 4*exp(-(44/351)*beta0^2*292008)` (approximately 0.920418), equivalently original complement mass at least ~0.079582. At H=23/24 required complementary masses are approximately 0.246494/0.393771, but these are numerical translations of thresholds and **not proven Haar masses**. The AKX scalar criterion is mathematically **impossible** for every H>=25, and that failure does **not** imply an original AJA witness.

Next source-level work: bridge the **unchanged original full one-slab spatial halfweights** to the ALC original pair-Haar Laplace expression using the certified centered source `f_H=(W_H-p_H)/2`, then prove a genuine physical norm lower bound. Separately, H22 genuine complementary Haar-cell certificate or another norm/top comparison is required for an unconditional AJA decision. No H-uniform coercivity, Hamiltonian mass gap or continuum 4D Yang--Mills mass gap established.

Operating rules: append-only / tighten-only / overwrite-forbidden / same-root.
