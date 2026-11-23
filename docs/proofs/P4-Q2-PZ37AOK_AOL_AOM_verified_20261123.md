# P4-Q2-PZ37AOK / AOL / AOM — original SU(2) Wilson fixed-left Haar moments and row response

Date: 2026-11-23 JST. **Formal-source integration and separate postmerge Lean revalidation: COMPLETED / SUCCESS**, restricted to the five public finite-volume theorems below.

## Canonical source and fixed verification context

- Repository: `itakura-hidetoshi/4d-mass-gap`; authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
- Latest verified Formal source HEAD after AOM: `1dc0e444472e2d3565bf82be7e14b4008981f0e1`.
- Exact pinned toolchain: Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Existing *original* Wilson SU(2) temporal crossing and one-slab action, normalized spatial compact-Haar probability measure, center twist, Gauss-law physical Hilbert and physical transfer setup are unchanged. No independent-plaquette surrogate or new hypotheses.
- Each theorem was tested in its actual `MGAP4D.MathlibAnalytic` module with dependency-aware Lean and `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` were present. No `sorryAx` and no changed-leaf warnings/errors.

## Exactly five new public declarations

**AOK**: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedLeftFullSlabCharacterV5_PZ37AOK.lean`

1. `p4Q2PZ37AOK_originalCrossingAction_fixedLeft_primaryCharacter_haar_zero` — for every finite `H` and every fixed left spatial configuration `A`, the true temporal crossing action has right-Haar pairing zero with the actual first spatial character: `∫ X_H(A,B) χ_H(B) dμ_H(B) = 0`.
2. `p4Q2PZ37AOK_originalOneSlabAction_fixedLeft_primaryCharacter_haar_eq_neg_eighth` — with the same fixed `A`, the original full one-slab action has right-Haar first-character moment `−1/8` (no left-boundary average).

**AOL**: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRelativeConditionalHaarRowV5_PZ37AOL.lean`

3. `p4Q2PZ37AOL_originalConditionalHaarRelativeTaylorResidual_abs_le_rowMass` — for `β ≥ 0`, `8β ≤ 1`, every `H,A`, the original conditional center-twist Taylor residual satisfies `|∫ R_{H,β,A}(B)χ_H(B)dμ_H(B)| ≤ 64β² ∫ K_{H,β}(A,B)dμ_H(B)`. The right-hand factor is the **actual positive Wilson row mass**, not a replacement constant.

**AOM**: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRowLocalLinearResponseV5_PZ37AOM.lean`

4. `p4Q2PZ37AOM_originalHaarPrimaryCharacter_antisymmetrization` — for every continuous real `F` on the genuine spatial configuration, the original Haar-preserving one-link center twist `τ` and odd first character give `−2∫F(B)χ(B)dμ = −∫(F(B)−F(τB))χ(B)dμ`.
5. `p4Q2PZ37AOM_originalFixedLeftRowLocalLinearResponse_abs_le` — for `β ≥ 0`, `8β ≤ 1`, every finite `H` and fixed `A`, the original, unnormalized first-character row response obeys `|−2∫K_β(A,B)χ(B)dμ(B) − β∫Δ(A,B)K_β(A,τB)χ(B)dμ(B)| ≤ 64β²`. The β-weighted coefficient remains interacting and is **not** replaced by its β=0 Haar moment.

These are Lean kernel results only within their stated finite-volume and coupling ranges; the formal structure-to-physics naming is an interpretive layer, not a separately proved physical continuum identification.

## CodeAI repair history: failed R2 retained; source-bound R3

The isolated diagnostic [PR #6903](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6903) (closed without merge) previously exposed five genuine Lean `Type mismatch` diagnostics at AOK 115:26, AOL 49:26 and 61:26, AOM 150:26 and 162:26 in [failed CI #45120638462](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45120638462). The annotation `Continuous (fun B : Cfg => (A, B) : Cfg × Cfg)` incorrectly made Lean expect a pair where the continuous *function* was required.

R3 made exactly five bounded source-notation corrections to `Continuous (fun B : Cfg => (A, B))`, without altering theorem statements or imports, and pinned the updated Git blobs within the same diagnostic commit `60ae12d7ca6ea24be6e0e67a6dfef6c36aaa87cf`. Final exact source blobs:

| Module | Unchanged adopted Git blob |
|---|---|
| AOK | `418c72d577e367e9cf6a948a8eee92729d97c0c3` |
| AOL | `61e54c15f9a1b603860d22421a1ae7b4feb739ff` |
| AOM | `dea992c87e4df0dffb88b2315f7dbe9c75298ac3` |

[Source-bound direct Lean + real `lean-lsp-mcp==0.30.0` #45123676116](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45123676116): all AOK/AOL/AOM direct and actual MCP jobs **completed/SUCCESS**, same source SHA256 before/after, five theorem axiom audits standard three only. The separate diagnostic [Lean Fast Check #45123676140](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45123676140) compiled **11,512/11,512** targets successfully.

The frozen KuuOS CodeAI helper version was `3c3d4a9127256fff732749fdfddd3118b30e86ab`. The repair and failures are preserved in append-only Proof Workbench as **observed, reuse=TEST_REQUIRED**, not an independently certified general-purpose CodeAI learning capability; its separate admission/independent-ensemble memory promotion remains HOLD.

## Exact-source independent PR and canonical postmerge CI

Every original research PR preserved the source blob above; after each prior Formal merge the next branch was brought forward by an **append-only two-parent commit**, not a source rebase/overwrite, and recompiled against the latest Formal source tree.

| Research PR | Latest premerge HEAD | Independent premerge CI | Formal squash HEAD | Independent Formal push CI | Exact source/testmerge/formal tree |
|---|---|---|---|---|---|
| [AOK #6899](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6899) | `b7255664596e0b9eb9b250f355e97d627af66870` | [#45124338822](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45124338822) SUCCESS | `1fe441c78434ca4e7c14bdf65a15d2053a46d40c` | [#45125939030](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45125939030) SUCCESS | `4282bf5a2852230c039f39e5c92dd8c49222f448` |
| [AOL #6901](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6901) | `d6593555d6f833c7dc0c0f19d6413d36a294069a` | [#45126286722](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45126286722) SUCCESS | `76a40c219cabbde174a03e045dc454995e4aa422` | [#45127105981](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45127105981) SUCCESS | `efe8ab28430c412bb7f575ee80455236b9956d49` |
| [AOM #6902](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6902) | `52c583abd024d2dde8f813ec1dcaff4170aa8515` | [#45127244976](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45127244976) SUCCESS | `1dc0e444472e2d3565bf82be7e14b4008981f0e1` | [#45128057549](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/45128057549) SUCCESS | `cc11e5990c02b63156c65983c5e028665daeef5e` |

For each row, source/testmerge/actual Formal Git trees were checked directly using GitHub MCP. Each exact premerge and postmerge Lean CI compiled **11,509/11,509**, required Lean step and exact-HEAD independent completion receipt **completed/SUCCESS**, only the three standard axioms for the new declarations, no sorryAx and zero changed-file warning/error.

Independent extraction [PR #6904](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6904) had isolated foundation Fast Check SUCCESS, but declared *the same public AOK and AOM theorem names*. It was **closed unmerged** to avoid duplicate declarations; its diagnostic historical source and CI remain preserved. PR #6903 was likewise closed unmerged after R3 adoption; no diagnostic files or disposable workflow were merged.

## Explicit obstructions and next theorem targets

This certification **does not** prove volume-uniform normalized physical top-state slope or spectral coercivity, a uniform positive physical Hamiltonian gap, an infinite-volume limit, the continuum scaling limit, or the full four-dimensional Yang–Mills existence-and-mass-gap problem. The two AOM formulas concern a genuine finite-volume unnormalized row and its still-interacting first derivative coefficient.

Any next gluing to a physical transfer-spectrum bound must independently establish the required normalization, sector projections, `H`-uniform compatibility and `β(H)` control. Retain unproven connection hypotheses as explicit obstructions rather than promoting these local Haar statements into a continuum mass-gap conclusion.

**Governance:** append-only, tighten-only, overwrite-forbidden, same-root; no changes to the original physical source, Lean/mathlib pins or verified antecedents.
