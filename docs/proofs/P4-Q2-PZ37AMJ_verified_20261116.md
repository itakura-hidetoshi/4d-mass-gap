# P4-Q2-PZ37AMJ — genuine original SU(2) Wilson finite-volume all-plaquette Gibbs covariance L¹

Date: 2026-11-16 JST. Mathematical result: **finite-volume uniform absolute connected covariance sum**, not a continuum mass gap.

## Canonical source and exact physical model

- Authoritative Formal branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Fixed Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; append-only / tighten-only / overwrite-forbidden / same-root.
- Original fixed physical SU(2) Wilson coupling: `beta0 = log(3/2)/64`; actual full interacting compact-Haar Gibbs law `mu[H,beta0]` at all original 4D physical positive links.
- Already-merged ancestors: AMF high-temperature conditional-Dobrushin certificate, AMG actual finite Gibbs connected plaquette covariance, AMH cyclic physical-time support separation, AMI true four-dimensional six-plaquette physical-link incidence and Green resolvent link-total.
- [Lean theorem PR #6797](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6797) **MERGED** as actual two-parent Formal canonical theorem commit `eac442f17d84c6856a3efa1ec8c475aaf1d3b207`. Parents: previous authoritative Formal `78702dc49612f34e63457210f95fcccad784ac9c` and exact certified source `7afe4a94d897b48bd6947d588018c65117d5dec0`.
- Exactly one new append-only Lean file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0AllPlaquetteGibbsCovarianceL1V5_PZ37AMJ.lean` (294 lines), with two new declarations and two explicit `#print axioms` audit commands. Existing Wilson/Haar/Gauss/AJA/physical OS transfer operators and proofs, pinned toolchain, roots, and workflows remain unchanged.

## New fully physical result

For every `H>0` and every **actual** oriented four-edge physical plaquette `p`, define `chi_p` as the original genuine SU(2) fundamental-character readout on the **full interacting Wilson configuration**, using `chi_p(A)=1-E(holonomy(A,p))` and `||chi_p||_infty<=1`.

Set `rho0 = 18*(exp(4*beta0)-1)/(exp(4*beta0)+1)`, certified `0 <= rho0 < 1` by AMF/AMG, independently of H.

The NEW Lean-certified theorem states for *all* actual physical plaquettes `q`, **without** a disjoint-support, spatial-distance, or other positive-separation hypothesis:

```text
∀ H > 0, ∀ p : ActualPhysicalPlaquette(H):
    SUM(q : ALL original 4D physical plaquettes)
      abs(Cov_(actual full Wilson Gibbs mu[H,beta0])(chi_q,chi_p))
      <= 96 / (1-rho0)
```

The right side is a volume-independent, finite explicit constant. This is not obtained from the previous coarse `24^D` graph-distance shell upper bound, since `24*rho0 > 1` there.

## Proof structure — two Lean declarations

1. `MGAP4D.MathlibAnalytic.compactOrientedGibbsCovariance_abs_sum_le_of_finiteFamilyGreenL1`: Generic, fully proof-relevant theorem on the **actual compact-Haar Wilson Gibbs system**. Let `F_i` be a finite family of bounded continuous left observables, each with a typed actual one-link oscillation profile `PF_i`, and `O` a right observable with an actual centered profile `P`. If for each link the sum over all `i` of `PF_i.variation` is bounded by `B>=0`, and the finite Dobrushin random-scan resolvent total variation of `P` is bounded by `R` for **every finite truncation M**, prove `SUM_i abs(Cov_Gibbs(F_i,O)) <= B*R`. The proof explicitly invokes the established exact Gibbs covariance random-scan telescope for each `i`, interchanges **finite** sums, applies pointwise nonnegativity, then proves the random-scan covariance remainders vanish in `M` and exchanges a **finite** family sum with the limit. No independent covariance inequality is postulated.
2. `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMJ_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l1_le`: Specialization on the unchanged actual original periodic SU(2) Wilson system, with `F_q=chi_q`, `O=chi_p`. The genuine per-link all-plaquette variation budget `B=12` is imported from AMI's proven physical incidence (at most six plaquettes touching any link, each coarse oscillation at most two). The actual original centered physical plaquette variation Green resolvent budget `R=8/(1-rho0)` is imported from AMI, giving `B*R=96/(1-rho0)` without weakening hypotheses.

In particular, AMJ's generic theorem proves the missing finite-family **Gibbs covariance** bridge; it is not merely a restatement of AMI's random-scan variation total.

## Version-bound elaboration repair — failure is preserved

- First source `5f91398bf474b3c5f6c03f31dd1371d9723c40ca`: [exact-source CI #43840838256](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43840838256) had a **failed required Lean step**, directly at the specialized theorem's `hFamily` proof line 226. The general finite-family Gibbs theorem independently elaborated and printed standard-three-only axioms. But a direct `change` on the sum of the constructed `ofFiniteSupport` profile variations was **not definitionally equal** to the sum of separately formulated physical support `if` terms; the failed specialized declaration's partial `#print axioms` included `sorryAx`. This earlier failed source is **not** a certified theorem.
- The failure was classified as a **proof-relevant dependent-field definitional-versus-propositional equality error**, not as an observed failure of the physical covariance bound. It was recorded append-only in PR #6797's discussion (GitHub comment ID `6912912011`).
- Repaired exact source `7afe4a94d897b48bd6947d588018c65117d5dec0`: Keeps both theorem statements and original constants. Instead proves the variation-field equality **for each real physical plaquette and link**, using fixed pinned `continuous_compact_oriented_ofFiniteSupport_variation_eq_two_mul_norm_of_mem` and `..._eq_zero_of_not_mem`, explicit `(C:=C)`, `(e:=e)`, and `Finset.sum_congr`, then applies AMI's already-certified ≤12 physical incidence theorem. No new sorry, axioms, weakened assumptions or mock observables.

## Independent exact-source Lean CI evidence

- [Exact-source PR CI #43842195242](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43842195242) `event=pull_request`, source HEAD `7afe4a94d897b48bd6947d588018c65117d5dec0`, workflow **completed/SUCCESS**.
- Main changed-Lean job `133213367332` and required `Run changed Lean fast check` step **completed/SUCCESS**; pinned dependency-aware build **11,513/11,513**.
- Both AMJ `#print axioms` outputs used ONLY `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; direct AMJ warnings and errors **0/0**.
- Separate independent exact-HEAD receipt job `133216800461` **completed/SUCCESS**. Actual receipt:
```text
event=pull_request exact_sha=7afe4a94d897b48bd6947d588018c65117d5dec0 source_result=success run=43842195242 attempt=1
```
- The exact source, GitHub synthetic test-merge `8f56a746dad227373cbd2fa4601accababe6aa0b`, and actual canonical Formal theorem merge `eac442f17d84c6856a3efa1ec8c475aaf1d3b207` share **Git tree `545a52f83a1b286365c47bee6a042a911e458745`**, separately retrieved through GitHub Git-object API.
- **Independent canonical postmerge push:** [event=push CI #43843337150](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43843337150) was initially observed **in_progress**, and is NOT retrospectively promoted here. Append the later actual exact-HEAD workflow/job/required-step/axiom/receipt evidence without overwriting this historical observation.

## Explicitly open obstructions and next research

- AMJ is a **fixed original beta0, finite-volume H-uniform susceptibility-type upper bound** on actual full interacting Gibbs connected correlations. It does not prove lower bounds on nonzero physical connected correlations, a physical OS one-slab transfer gap, Hamiltonian spectral gap, Gauss-law-compatible cross-H Hilbert transport, factorial coupling `beta(H)` compatibility, or a 4D continuum Yang--Mills mass gap.
- It does **not** by itself prove physical four-dimensional Euclidean-distance exponential decay from AMH's one-coordinate statement, or a polymer/continuum limit at changing beta.
- Original H=0 degenerate two-site even periodic side length remains outside the strict n>=3 uniqueness used here.
- KuuOS CodeAI and standalone Lean MCP execution receipts remain **NO_DATA**; the authoritative machine proof evidence in this stage is exact-source and canonical GitHub Actions Lean, not an asserted unobserved external agent.
