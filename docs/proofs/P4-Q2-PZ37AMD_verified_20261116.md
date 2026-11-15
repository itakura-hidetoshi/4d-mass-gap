# P4-Q2-PZ37AMD — certified actual SU(2) primary-plaquette fundamental character coefficient

Date: 2026-11-16 JST. Theorem [PR #6779](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6779) **MERGED** into authoritative `formal/real-hilbert-uniform-coercive-strong-limit` with exact two-parent canonical commit `69ed84590a06cf0f6ecfea10abfe0cba6e744a2e`.

## Exact mathematical claim and limitation

One NEW append-only 167-line Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteFundamentalCharacterCoefficientV5_PZ37AMD.lean`.

Existing [AMB #6775](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6775) and [AMC #6776](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6776) prove the **actual four distinct physical links** of the canonical oriented primary SU(2) spatial plaquette, conjugation equivalence to true cyclic holonomy `Phi_H`, actual full boundary product-Haar pushforward, original Wilson local Boltzmann mass and unweighted character moments.

Existing ABN (imported via `PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN.lean`) already proved for the genuine original SU(2) Wilson/Haar character `chi=1-E` and original nonnegative coupling `beta` the **nontrivial** coefficient bound `beta*exp(-2*beta)/4<=r_ABN(beta)<=1`. AMD does **not** claim this ABN inequality was newly derived.

AMD directly proves equality of the ACTUAL primary-plaquette weighted character moment and positive mass with the ABN original SU(2) integrals, then defines their normalized ratio `r_primary(H,beta)` and proves the EXACT identity

```text
r_primary(H,beta) = r_ABN(beta)      (all H, all real beta).
```

Because the *free product-Haar* mean of the true primary plaquette character is zero, the single-plaquette connected covariance with its original Wilson Boltzmann weight is genuinely bounded:

```text
Cov_free-Haar(chi(Phi_H), exp(-beta * E(Phi_H)))
  >= beta * exp(-2*beta) / 4  (beta>=0).
```

At unchanged original `beta0=log(3/2)/64`, for **every true finite H**, `0<beta0*exp(-2*beta0)/4<=r_primary(H,beta0)<=1`. The coefficient is a local four-link physical plaquette observable, not a surrogate and **not the nontrivial spectrum of the full interacting Wilson transfer**.

**No assumption** of independence of two different plaquettes or any new physical kernel/measure. The true interacting Wilson Gibbs distribution differs from the free-Haar reference and its multi-plaquette connected cluster coefficients remain UNPROVED. No cross-H Gauss-law Hilbert embedding, independent ALY/ALZ norm comparison, uniform beta0 transfer gap, Hamiltonian or continuum 4D Yang–Mills mass gap follows.

## Full seven-declaration audit

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`; common prefix `p4Q2PZ37AMD_`:

1. `originalPrimaryPlaquetteWilsonCharacterCoefficient` (definition)
2. `primaryPlaquetteWilsonCharacterMoment_eq_originalABN`
3. `primaryPlaquetteWilsonMass_eq_originalABN`
4. `originalPrimaryPlaquetteCoefficient_eq_originalABN`
5. `primaryPlaquetteWilsonCharacter_connectedHaar_ge`
6. `originalPrimaryPlaquetteCoefficient_ge`
7. `originalFixedBeta0_primaryPlaquetteCoefficient_certificate`

## Exact version-bound Lean4 repair and CI provenance

- Baseline canonical formal `163027ddebc5d24697fecaa84efbeac33018933d`.
- Initial source `717b25e4c4b18edf8a26cf045280c1f812b3ad41`: [initial source CI #43773246230](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43773246230) changed-Lean step **FAILURE**, exactly one AMD direct error at line 147 `failed to prove positivity/nonnegativity/nonzeroness`. Lean `positivity` did not discover previously proved `p4Q2PZ37ADC_fixedCoupling_pos` needed to show the original beta0 floor positive. Other six declarations printed only standard-three axioms, but the failed final declaration carried `sorryAx` via elaboration recovery. Never certify the whole initial source.
- Repair source HEAD `3b71d89e17c56f9a2397d68e0e69a2b513509e46` adds **only an explicit proof term** `div_pos (mul_pos p4Q2PZ37ADC_fixedCoupling_pos (Real.exp_pos _)) (by norm_num)` to the original final theorem. No theorem signature, physics, beta0, roots, imports or toolchain pins are weakened.
- [Exact-source PR CI #43773899078](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43773899078): workflow and Lean job **completed/SUCCESS**, pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, full dependency closure **11,461/11,461**, seven `#print axioms` outputs use only `propext`, `Classical.choice`, `Quot.sound`; no new `sorryAx`, changed AMD warning/error 0/0. Independent receipt job `132997111824` **completed/SUCCESS** and actual receipt:
  `[mcp-receipt] event=pull_request exact_sha=3b71d89e17c56f9a2397d68e0e69a2b513509e46 source_result=success run=43773899078 attempt=1`.
- Exact source/synthetic test-merge/real canonical merge share **Git tree `a3e7f2620a830830ec248946278cc3b6c7362ff8`**. The canonical merge has base parent `163027ddebc5d24697fecaa84efbeac33018933d` and exact repaired source parent `3b71d89e17c56f9a2397d68e0e69a2b513509e46`.
- Separately triggered **postmerge event=push CI [#43774439459](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43774439459)** on canonical `69ed84590a06cf0f6ecfea10abfe0cba6e744a2e` was initially **in_progress**. This historical state is preserved; certify its future outcome **only** after workflow/job/Lean step/exact-head completion receipt independently complete and add a separate appended observation.

**CodeAI / Lean MCP execution receipt**: NO_DATA in this GitHub-MCP-only session; the independent checker is GitHub Actions pinned Lean, not an unobserved CodeAI process.

## Next independent physical obstruction

True `SU(2)` Wilson single-plaquette coupling coefficient is now attached to an actual four-edge primary plaquette, but it is still under free Haar. Next independent mathematical target is to control two **distinct** neighboring plaquettes with shared links in the actual interacting Wilson Gibbs/one-slab transfer, prove explicit volume-uniform cluster constants compatible with the Gauss-law Hilbert sector, then connect to genuinely physical ALY/ALZ cross-volume ratios or a direct uniform spectral criterion. The all-H beta0 transfer gap, Hamiltonian gap and continuum 4D Yang–Mills mass gap remain **OPEN/NO_DATA**.


## Independent canonical postmerge push certification — 2026-11-16 JST

The historical *in_progress* state above remains recorded as observed then. The independently re-observed [event=push workflow #43774439459](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43774439459) on the **actual integrated canonical formal HEAD `69ed84590a06cf0f6ecfea10abfe0cba6e744a2e`** is now **completed/SUCCESS**. Main changed-Lean job `132997374925`, required `Run changed Lean fast check` step and independent completion receipt job `132999310483` all completed/SUCCESS.

Real pinned Lean dependency closure **11,461/11,461**; all **7/7** original AMD `#print axioms` prints only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`, AMD changed-file warning or error. Exact issued completion receipt:

```text
[mcp-receipt] event=push exact_sha=69ed84590a06cf0f6ecfea10abfe0cba6e744a2e source_result=success run=43774439459 attempt=1
```

The merged canonical Git tree `a3e7f2620a830830ec248946278cc3b6c7362ff8` matches exact source and GitHub synthetic test merge. This verifies the actual four-edge free-product-Haar primary-plaquette coefficient and **single-plaquette** connected covariance, not interacting full Wilson multi-plaquette clustering or a transfer/Hamiltonian/continuum mass gap.
