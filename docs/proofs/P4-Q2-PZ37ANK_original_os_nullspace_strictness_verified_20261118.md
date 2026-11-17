# P4-Q2-PZ37ANK — original Wilson OS null-space criterion and beta-zero strict positivity

2026-11-18 JST. Authoritative theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`, repository `itakura-hidetoshi/4d-mass-gap`. Fixed Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only / tighten-only / overwrite-forbidden / same-root. This record adds no Lean code; docs-only changes must not rerun Strict Lean.

## Certified mathematical scope

Retain the exact original ANF full-periodic SU(2) Wilson Gibbs OS quadratic form, time-one two-mode observable, boundary Gram moment M, partition function and Haar factors. For every finite H and beta >= 0, the actual boundary moment is integrable and in L2, and its norm-square is integrable. Consequently:

```text
Q_OS(H,beta,c0,c1) = 0 iff M(H,beta,c0,c1) = 0 boundary-Haar almost everywhere.
Q_OS(H,beta,c0,c1) > 0 iff M(H,beta,c0,c1) is not boundary-Haar a.e. zero.
Nonzero boundary-Haar mean of M implies Q_OS > 0.
At beta = 0, c0 != 0 implies Q_OS > 0 (all finite H, including H=0).
At beta = 0, Q_OS = 0 implies c0 = 0.
```

The last two statements use ANJ's exact first boundary moment `sqrt(Z_H(0)^(-1))*c0`. The integrability required to infer an a.e. zero function from a zero nonnegative Bochner integral is proved, not assumed. No ordinary Gibbs/Haar L2-nonzero statement is promoted to OS positivity.

## Exact source and declarations

File: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicTimeOneOSNullSpaceStrictnessV5_PZ37ANK.lean` (314 added lines, no deletions of existing source). Eleven theorems, each with a matching axiom print:

1. `p4Q2PZ37ANK_originalTimeOneGramFeature_norm_le`
2. `p4Q2PZ37ANK_originalTimeOneGramFeature_joint_integrable`
3. `p4Q2PZ37ANK_originalTimeOneBoundaryMoment_integrable`
4. `p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_le`
5. `p4Q2PZ37ANK_originalTimeOneBoundaryMoment_memLp_two`
6. `p4Q2PZ37ANK_originalTimeOneBoundaryMoment_norm_sq_integrable`
7. `p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_zero_iff_boundaryMoment_ae_zero`
8. `p4Q2PZ37ANK_originalTimeOneWilsonOSQuadratic_pos_iff_boundaryMoment_not_ae_zero`
9. `p4Q2PZ37ANK_originalTimeOneOSQuadratic_pos_of_boundaryMean_ne_zero`
10. `p4Q2PZ37ANK_originalBetaZeroOSQuadratic_pos_of_c0_ne_zero`
11. `p4Q2PZ37ANK_originalBetaZeroOSQuadratic_zero_implies_c0_zero`

## Exact-source CI and Formal integration

- Theorem [PR #6871](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6871): MERGED.
- Original Formal base: `46777bde184158ed375a2f3686be2b99b7ec6b44`.
- Certified source HEAD: `d18dfef9a35600aef556dc1a3e4af3f19e9f037e`.
- Source blob: `68d1927852cf587e2215572c82c6017fbacc91d9`, independently computed from the complete local source and matched to integrated GitHub source.
- Synthetic test-merge: `416cf4a512a55c0a1146a1cd0ef1ee2718560261`.
- Actual Formal theorem integration: `a7e774b39a948e26e3f383d55c3e4a1125bd3384`.
- Live GitHub source/test-merge/integration tree: `8086b5a584d554e5f121ccc2527d5ccc3efffcc1`, all three equal. These values were re-read from the immutable Git commit endpoints, rather than copied from conversational memory.
- [Exact-source CI #44189672864](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44189672864): completed/SUCCESS.
- Source Lean job `134415398863`, required Lean step completed/SUCCESS, build `8880/8880`.
- Source receipt job `134417131499`, completed/SUCCESS; actual log `event=pull_request exact_sha=d18dfef9a35600aef556dc1a3e4af3f19e9f037e source_result=success run=44189672864 attempt=1`.
- Source diagnostic artifact `14375353972`, SHA256 `81d42e1bc2f57d3d3aab95c8c2d614e3fd7b1869ddf47ca013eadb9750c94d05`.

## Independent canonical push verification

[Formal push CI #44190450681](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44190450681): event=push, exact integrated HEAD `a7e774b39a948e26e3f383d55c3e4a1125bd3384`, workflow completed/SUCCESS. Distinct Lean job `134418133116` and required Lean step completed/SUCCESS; build `8880/8880`. Diagnostic artifact `14377585487`, downloaded and SHA256-verified as `5cf89b7514115b49a1bdd0cb86c207d10ce79a7ce5dd090c451331c40c9b79f6`.

All eleven requested axiom outputs were compared with the actual source inventory in BOTH source and push logs: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; ANK warnings/errors 0/0. Imported dependencies can have existing warnings; no global warning-free claim.

Distinct push receipt job `134420658696`, completed/SUCCESS, with actual log:

```text
[mcp-receipt] event=push exact_sha=a7e774b39a948e26e3f383d55c3e4a1125bd3384 source_result=success run=44190450681 attempt=1
```

Status: **FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED**, for these eleven finite-volume ANK theorems only. Receipt success is not used as a substitute for the full Lean log and axiom audit.

## Repair provenance retained, not overwritten

The same PR retains failed candidate commits and their diagnostic observations. In particular:

- Baseline `3957fea29ecba8ef2f0ea3e8deae78c8c0708e0e` / blob `cd7dfbc7eb7a87da40fc1859be0da48fd62796bc` contained an unnecessary proof-local SFinite declaration. The square-integrability proof uses the pinned `Integrable.of_bound` finite-measure interface; deleting the extra declaration preserves the original finite Haar measure and assumptions.
- Candidate `3d7d1deebd5ef922481d872117e6f5378814f0cc` / blob `5f447e8503fd3d1415d7c5ee85cbf2c37760a4fc`, run `44188888613`, failed at the null-space theorem, not at square integrability. The first six declarations printed standard axioms, but that partial success did not certify the file. Diagnostic artifact SHA256: `f292ec771bf5d46e844c74fd7a8ff8c25cf7be7152b30db8052fcd8f68fff8dc`.
- The remaining hypothesis was `norm(M b)^2 = 0 b`; restricted `simpa only [sq_eq_zero_iff, norm_eq_zero]` did not first reduce the zero-function evaluation. The successful source explicitly uses `change ... = (0 : Real) at hb`, then `norm_eq_zero.mp (sq_eq_zero_iff.mp hb)`. This is definitional conversion, not an added premise. All eleven theorem signatures and imports stayed unchanged across these two repairs.
- Failed-build downstream `sorryAx` printouts are retained as failure evidence, never accepted as certification.

## Actual CodeAI use and unrun stages

Unchanged bounded extractions of KuuOS `git_blob`, `query_cases` and `route_candidates` were actually executed from `runtime/kuuos_codeai_lean_failure_memoryos_v0_1.py`, KuuOS ref `646d14042a5fe556cd5d625d99024e55f34e4996`, upstream blob `9f86641e60d0e76fafd8d850e7053d5e1cae6df8`. This was candidate management, not autonomous theorem generation or the full runtime. External memory history was NO_DATA (`cases=[]`); an outer guard rejected nonempty history rather than weakening upstream validation or relabelling cross-root memory.

The selected scalar-zero candidate is blob `68d1927852cf587e2215572c82c6017fbacc91d9`; the alternate Pi-zero simplification candidate `9594032626455a475f8242cbc83facce160fe8bc` remains untested. The routing receipt's `selects_proof=false` and `independent_ci_certified=false` describe its pre-CI state and are not retroactively rewritten. The later GitHub Actions runs are separate proof evidence.

Local direct Lean: NOT_RUN. Independent Lean MCP: NOT_RUN. The actual verifier was pinned Lean running in GitHub Actions; no four-stage-runtime completion is claimed.

## Remaining obstruction and next scientific target

The selected physical top-eigenspace-orthogonal coefficient pair is not proved to have `c0 != 0`; the converse `c0=0 -> Q_OS=0` is not asserted. H=0 is the antipodal fixed-slice case, while H>0 has a strict positive interior; the exact fixed-boundary fiber mean still needs that geometry. For the original beta-positive physical excitation, prove nonvanishing of the actual boundary moment, or establish a null-space obstruction, without substituting another observable, measure or operator.

Physical OS quotient identification, original Wilson one-slab/completed OS boundary-operator intertwining, a volume-uniform gap and continuum four-dimensional Yang–Mills construction/mass gap remain unproved. This historical record is not a substitute for the Lean source and actual kernel/CI evidence.
