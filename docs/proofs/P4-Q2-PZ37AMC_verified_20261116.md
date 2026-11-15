# P4-Q2-PZ37AMC — genuine original SU(2) primary plaquette Wilson Haar Boltzmann coefficient

Date: 2026-11-16 JST. [AMC theorem PR #6776](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6776) **MERGED** into authoritative formal at canonical two-parent commit `95d9290ef8a7053cf36eb91a5b772367cd9a23d8`. Parent theorem AMB [#6775](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6775) is independently certified as actual four-edge SU2 Haar holonomy transport.

## Exact unconditional *local* original Wilson model result

One NEW append-only Lean file:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteWilsonBoltzmannCoefficientV5_PZ37AMC.lean`.

The **actual oriented** four-edge physical plaquette holonomy `A(a) A(b) A(c)^(-1) A(d)^(-1)` has original fundamental Wilson character equal pointwise to that of the corresponding cyclic boundary-holonomy `Phi_H`, by the existing conjugation-invariant *unchanged* Wilson energy and actual boundary restriction. This is shown for arbitrary genuine full edge configuration, without an assumed independent plaquette distribution.

AMB's theorem-generated normalized-Haar pushforward gives for each finite H and all real beta:

```text
integral_{true boundary product Haar mu_H} exp(-beta * E_original(Phi_H))
    = z_original_SU2(beta)
    = integral_{true normalized SU2 Haar nu} exp(-beta * E_original(g)).
```

This exact primary physical plaquette *Haar reference* coefficient equals the original AIF genuine SU2 one-link Wilson Boltzmann integral — no new probability law or modified action. At the **original fixed** `beta0=log(3/2)/64`, positivity (AIF) and variance-sensitive upper bound (AKW) yield, **without new physical premises**, for every H:

```text
0 < integral_muH exp(-beta0 * E_original(Phi_H))
  <= exp(-beta0 + (44/351)*beta0^2).
```

This is an actual one-plaquette/trivial-representation Boltzmann coefficient, **not a proof** that interacting plaquette products factor, that a nontrivial fundamental-character cluster expansion is summable, or that the original physical full one-slab operator has an H-uniform gap.

## Four exact new declarations

All under `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` prefix `p4Q2PZ37AMC_`:

1. `originalOrientedPrimaryPlaquetteCharacter_eq_cyclic`.
2. `primaryPlaquetteWilsonHaar_partition_eq_original`.
3. `originalFixedBeta0_primaryPlaquetteWilsonHaar_pos`.
4. `originalFixedBeta0_primaryPlaquetteWilsonHaar_le`.

Four matching `#print axioms` commands, with no new assumptions or sorry.

## Machine certification and provenance

- Exact source HEAD `7a3df44e3db0f65dfbecbb1af7d1c0cf1085a466`, base canonical AMB merge `1e141c99ba8c8b2f9ffd6203f9dbabb838ad4233`.
- [Exact-source PR CI #43764567401](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43764567401) **completed/SUCCESS**, changed-Lean dependency closure **11,460/11,460** with pinned Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Exact **4/4** new axiom outputs contain only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx` and changed AMC warning/error 0/0. Changed Lean job `132966651956` and independent exact-source receipt job `132968394875` completed/SUCCESS; observed
  `[mcp-receipt] event=pull_request exact_sha=7a3df44e3db0f65dfbecbb1af7d1c0cf1085a466 source_result=success run=43764567401 attempt=1`.
- Source, synthetic test merge and actual canonical merge share exactly Git tree `f5a24cad79c9472424b7cda5a541f12e5be151d7`; canonical `95d9290ef8a7053cf36eb91a5b772367cd9a23d8` has the exact base/source parent ancestry.
- Separately triggered [actual canonical event=push CI #43765204840](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43765204840) was initially seen **in_progress**. This initial observation is retained; the future result must be re-observed before certification and appended separately. The source PR success is not a postmerge push success.
- CodeAI/Lean MCP execution receipt: **NO_DATA** (GitHub MCP and GitHub CI only).

## OPEN obstruction

Actual multiple-plaquette connected SU2 character/cluster coefficients with overlapping links, **uniform-in-volume** small constants for the interacting Wilson Gibbs and original fixed-beta0 one-slab transfer norm, Gauss-law-compatible typed cross-volume maps, ALY/ALZ independent summable raw/full budgets, H-uniform transfer gap, Hamiltonian and continuum 4D Yang–Mills mass gap all remain **OPEN/NO_DATA**. Do not promote this one-plaquette identity into any of these unsupported global claims.
