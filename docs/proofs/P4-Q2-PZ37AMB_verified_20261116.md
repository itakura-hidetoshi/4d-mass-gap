# P4-Q2-PZ37AMB — authenticated genuine primary SU(2) plaquette Haar character moments

Date: 2026-11-16 JST. Authoritative theorem branch `formal/real-hilbert-uniform-coercive-strong-limit`. [AMB PR #6775](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6775) **MERGED** as canonical two-parent commit `1e141c99ba8c8b2f9ffd6203f9dbabb838ad4233`.

## Unconditional genuine local physical geometry

One new append-only Lean file `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteHaarCharacterBridgeV5_PZ37AMB.lean`, retaining the original normalized SU(2) compact Haar and true four **distinct** physical primary spatial plaquette boundary links. Its exact cyclic holonomy `Phi_H=c^(-1)d^(-1)ab` is conjugate to the physically oriented plaquette `ab c^(-1)d^(-1)` (imported physical class-function geometry theorem).

The existing true product-Haar pushforward theorem `measurePreserving_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy` (physical four-edge boundary configuration, not independent fake plaquettes) is combined with existing original SU(2) character `chi=1-E` and independently verified true Haar moment declarations (AIQ/ACK/AKW). Therefore on the **actual full reflection-fixed boundary product Haar reference measure** `mu_H`:

```text
E_{mu_H}[chi(Phi_H)]   = 0
E_{mu_H}[chi(Phi_H)^2] = 1/4
E_{mu_H}[exp(beta*chi(Phi_H))] <= 1+44*beta^2/351,
                                  0<=beta<=1/156.
```

The exponential bound is specialized to the **unchanged** physical `beta0=log(3/2)/64`. All claims hold at *each actual finite H*, without an added physical hypothesis. This does NOT assert a second plaquette is independent, the interacting Wilson Gibbs law equals product Haar, a true two-volume raw/full transfer estimate, summable cluster expansion, or any mass gap.

## New exact declaration list

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`, common prefix `p4Q2PZ37AMB_`:

1. `primaryPlaquetteHaar_integral_transport` — actual four-edge Haar pushforward, arbitrary AEStronglyMeasurable real test function.
2. `primaryPlaquetteCharacter_Haar_mean_zero`.
3. `primaryPlaquetteCharacter_Haar_secondMoment`.
4. `primaryPlaquetteCharacter_Haar_mgf_le`.
5. `originalFixedBeta0_primaryPlaquetteHaar_mgf_le`.

All five declarations have matching `#print axioms`.

## Actual version-bound Lean failure and proof-only repair provenance

- Initial source HEAD `7a9b4b4a90723cd35a3abdfafe4c39b6c3bec509`, [CI #43763080385](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43763080385): changed-Lean **FAILURE** at line 122, `fun_prop` could not discover the original `p4Q2PZ35C_originalOneLinkCharacter` continuity theorem. The diagnostic explicitly states no tactic-database theorem for the custom function; this is not mathematical discontinuity. First three local declarations printed only the standard three axioms, but the two dependent declarations carried `sorryAx` by elaboration failure recovery and are **NOT certified** for this source.
- Final proof-only repair HEAD `747013bacdbdd79943d3c7c45859197ccf1a54ec` replaces `fun_prop` by explicit `Real.continuous_exp.comp (continuous_const.mul p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous)`. No theorem statement, hypothesis, Wilson kernel, Haar law, AJA, beta0, root, or pin changed.
- [Exact-source PR CI #43763739841](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43763739841) **completed/SUCCESS**, fixed Lean `v4.30.0-rc2` and pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; actual changed-Lean dependency closure **11,459/11,459**; all **5/5** exact `#print axioms` outputs only `propext`, `Classical.choice`, `Quot.sound`; no new `sorryAx`, changed AMB warning/error 0/0; independent source receipt:
  `[mcp-receipt] event=pull_request exact_sha=747013bacdbdd79943d3c7c45859197ccf1a54ec source_result=success run=43763739841 attempt=1`.
- Same source/test-merge/ACTUAL canonical merge Git tree `8dfa25d3c5c554ee27376611fb875ea093d6d275`. The canonical merge parents are former formal `261fe9e4454319c0f5df022e38fbaa8ec43b34ab` and repaired source `747013bacdbdd79943d3c7c45859197ccf1a54ec`.
- Independent [canonical event=push CI #43764326088](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43764326088) on exact canonical HEAD `1e141c99ba8c8b2f9ffd6203f9dbabb838ad4233` **completed/SUCCESS**, Lean **11,459/11,459**, 5/5 standard-three-only axioms, no AMB sorryAx or changed warnings/errors. Changed Lean job `132965905024` and independent completion receipt job `132967721561` both completed/SUCCESS:
  `[mcp-receipt] event=push exact_sha=1e141c99ba8c8b2f9ffd6203f9dbabb838ad4233 source_result=success run=43764326088 attempt=1`.

**CodeAI/Lean MCP execution receipt:** NO_DATA in this sequence; independent checker was GitHub CI, not an unobserved local CodeAI process.

## Remaining actual physical obstruction

The primary-plaquette free-product-Haar coefficient is exact; interaction-induced multi-plaquette connected cluster bounds, *volume-independent* decay constants in the true SU(2) Wilson Gibbs/one-slab transfer law, Gauss-law/Haar-compatible **cross-H** Hilbert transport, the independent ALY/ALZ raw/full norm comparison, and the uniform beta0 transfer/Hamiltonian/continuum 4D Yang–Mills mass gap are **OPEN/NO_DATA**. This declaration does not assert those results.
