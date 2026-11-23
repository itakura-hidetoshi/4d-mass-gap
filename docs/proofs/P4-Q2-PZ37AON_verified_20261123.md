# P4-Q2-PZ37AON — original Wilson SU(2) zero-coupling Haar action-gap coefficient

Date: 2026-11-23 (JST). **Two public theorems formally integrated and independently revalidated after merge.** Only the actual original finite-volume Wilson/Haar model is used.

## Authoritative source and fixed environment

- Repository: [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap); authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`.
- Exact Lean-source canonical merge commit: `775c40921d2d87ec964b87a54db7e17ed1b42452`. Docs-only updates after this commit do not replace the independently verified Lean-source SHA.
- Source: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalZeroCouplingHaarGapV5_PZ37AON.lean`; Git blob `37d17471fc11a8bcd7a0dbad6021d4f679c7c405`; SHA-256 `024d48dfb0b8c813c5fa58c99f25d5756588c16cdd6dbd3d1e9e180c8c800c30`.
- Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; original SU(2) Wilson action, Haar product probability, one-link center twist, Gauss-law physical Hilbert and all existing definitions/pins unchanged.
- Appendix-only source; old public theorems and their assumptions were not edited, weakened or redefined.

## Exactly two new Lean theorems

1. `p4Q2PZ37AON_originalFixedLeftCenterTwistGap_primaryHaar_eq_neg_quarter` proves, for **every finite H** and **every fixed original left spatial boundary A**, the genuine AOH action difference `Δ_H(A,B) := S_H(A,B) − S_H(A,τ B)` satisfies

   `∫ Δ_H(A,B) χ_H(B) dμ_H(B) = −1/4`.

   Here `χ_H` is the existing original first spatial character, `τ` is the existing Haar-preserving one-link center twist, and `μ_H` is the existing normalized compact spatial Haar product measure. The proof applies the certified AOM antisymmetrization to the **continuous genuine one-slab action** `F(B)=S_H(A,B)` and the certified AOK fixed-left moment `∫S_H(A,B)χ_H(B)dμ_H(B)=−1/8`. It does not average over A, introduce any independent-plaquette measure, or use a surrogate action.

2. `p4Q2PZ37AON_originalZeroCouplingFlippedKernelGap_primaryHaar_eq_neg_quarter` restores the **literal original Wilson kernel** `K_{H,0}(A,τ B)=exp(−0·S_H(A,τ B))=1`, proving

   `∫ Δ_H(A,B) K_{H,0}(A,τ B) χ_H(B) dμ_H(B) = −1/4`.

   This is an exact beta **zero** identity. The `β>0` coefficient `∫Δ_H K_{H,β}(A,τ B)χ_H dμ_H` remains interacting, and its volume-uniform proximity to `−1/4` is **not proved by AON**.

## Source-bound KuuOS CodeAI sandbox precedes independent CI

To enforce direct Lean **before** expensive independent CI, [diagnostic PR #6906](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6906) stored the candidate as a `.lean.txt` file only, Git blob `37d17471fc11a8bcd7a0dbad6021d4f679c7c405`. Its isolated GitHub Actions runner verified the exact Git blob and fixed pins, staged those identical bytes as `.lean` **only in its temporary filesystem**, compiled the actual AOK/AOM imports, ran direct Lean with `warningAsError`, checked both printed axiom lists, then and only then invoked `lean-lsp-mcp==0.30.0` for complete nonpartial typed diagnostics and source-bound axiom matching.

[Direct Lean and real MCP run #45130040535](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45130040535) completed/SUCCESS, with 2/2 public declarations depending on only `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` absent and changed-file warnings/errors zero. Source SHA-256 before/after remained `024d48dfb0b8c813c5fa58c99f25d5756588c16cdd6dbd3d1e9e180c8c800c30`. The temporary source was not promoted by this run, and the ordinary independent PR CI did **not** run on that diagnostic branch.

Only after the direct/MCP PASS were the **same source bytes** adopted into [research PR #6907](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6907), head `aaa8d0779953e4e11d4d89286a18387f45ffee80`.

## Independent exact-head proof and canonical postmerge receipt

| Gate | Independently observed result |
|---|---|
| [Premerge PR Lean #45130654802](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45130654802) | workflow, Lean job and exact-head receipt completed/SUCCESS; **11,512/11,512** Lean |
| Public axiom audit | AON **2/2**, standard `propext`, `Classical.choice`, `Quot.sound` only; `sorryAx` absent; changed warning/error 0/0 |
| Formal squash commit | `775c40921d2d87ec964b87a54db7e17ed1b42452` — [PR #6907](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6907) MERGED |
| Source / test-merge / Formal Git tree | all exactly `57511c8c249ec893cf4d71a29acb1d8c303875e4` |
| [Postmerge push CI #45131375523](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45131375523) | required Lean job, pinned build **11,512/11,512**, new axiom outputs 2/2 standard-three only, independent exact-HEAD receipt completed/SUCCESS |

Diagnostic PR #6906 was closed **without merging**; its archived temporary source, workflow and receipts are retained for provenance. KuuOS CodeAI revision `3c3d4a9127256fff732749fdfddd3118b30e86ab` supplied pinned tests and real Lean MCP validators. Proof Workbench preserves source-bound observations **append-only**, but generic MemoryOS learning/admission has NOT been certified and must remain `TEST_REQUIRED` for reuse on other source HEADs.

## Current obstruction to further gluing

Let `D_H(β,A) := ∫ Δ_H(A,B) K_{H,β}(A,τ B) χ_H(B)dμ_H(B)`. **AON proves only `D_H(0,A)=−1/4`**, independently of finite H and fixed A.

AOM separately proves for `β≥0`, `8β≤1` the H-uniform *relative-to-the-true-interacting-coefficient* estimate

`|−2∫K_{H,β}(A,B)χ_H(B)dμ_H(B) − β D_H(β,A)| ≤ 64β²`.

To replace `D_H(β,A)` by `−1/4` at `β>0`, a new estimate with explicit **uniform-in-H** control of `D_H(β,A)−D_H(0,A)` is required. A single fixed-H continuity or Taylor statement would **not** discharge this obstruction. Nor do these unnormalized row results establish normalization of the Gauss-law physical top state, a uniform Hamiltonian gap, an infinite-volume limit, continuum scaling or the full four-dimensional Yang–Mills existence-and-mass-gap theorem.

Governance: `append-only / tighten-only / overwrite-forbidden / same-root`. Interpretation of formal coefficients as physical continuum claims is separate from what the Lean kernel certified.
