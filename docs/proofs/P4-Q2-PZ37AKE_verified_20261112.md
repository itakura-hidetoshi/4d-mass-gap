# P4-Q2-PZ37AKE — 元AJA有限冪証人の持続性と真正Wilson冪の条件付き厳密判定

2026年11月12日 JST。固定Lean4形式検証の説明記録。この文書自体はLeanカーネルによる証明ではない。

## 1. Canonical source and mechanical receipts

- Repository: `itakura-hidetoshi/4d-mass-gap`; only theorem canonical branch: `formal/real-hilbert-uniform-coercive-strong-limit`. `main` is a separate publication mirror.
- [定理PR #6666](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6666) MERGED; certified final source HEAD `a82d74542653d42c4d564486429934d29c6eb47f`; formal squash HEAD `08e4fe2a92df2595cbfb2da141baa588e44d9eea`.
- [Exact-source CI #43115696190](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43115696190): workflow, changed-Lean job, actual Lean step, and independent completion receipt all completed/SUCCESS. 11,444/11,444 Lean dependency closure; eight new declarations, eight independently printed axiom sets, solely `propext`, `Classical.choice`, `Quot.sound`; changed Lean warning/error 0/0; forbidden-token audit `sorry: 0`; no new `sorryAx`.
- [Post-merge independent formal push CI #43116444718](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43116444718): event=push at exact squash HEAD, workflow/job/Lean step/receipt completed/SUCCESS, 11,444/11,444 Lean, 8/8 standard-only axiom audits, changed warning/error 0/0, source commit receipt `chatgpt-ci-receipt/PR Lean Fast Check` success.
- Source, GitHub real test-merge, and actual formal squash Git tree are all `92499907d8cf255b1de62e45bccc5e6c5c9a71c6`, identity checked. New Lean leaf blob `4ed3b4ebd916c23a4868efb87d97f645e210c6e4`.
- Previous exact-source [#43113923868](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43113923868) and [#43114919363](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43114919363) both completed/SUCCESS; subsequent HEAD changes were append-only same-proof merge synchronization with concurrently integrated AKD theorem and AKD record. No rewriting of old proofs or edits to existing Lean files.
- Single new file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAJAEventualPowerWitnessV5_PZ37AKE.lean` (278 added lines, 0 deletions); direct imports AKC, AJZ, AJV, mathlib orthogonal projection and tactic. Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## 2. What was kernel-checked (scope is all finite H and beta>0)

Let S be the **original** normalized physical SU(2) Wilson transfer, f0 the **original** signed centered ZW physical L2 source, V=||f0||²>0 the unchanged original Haar variance, Q the projection onto the **full** top-fixed eigenspace, R the true top-orthogonal restriction, and B>0 the **original** AJA strict-negative-Haar-region margin²×real Haar mass. Let C=(original AJU defect floor/2)²>0 be the true AJV q-free correction.

1. **Unconditional energy monotonicity:** for any natural n≤k, `||S^k f0||² ≤ ||S^n f0||²`, using the actual `||S||=1`.
2. **Strict witness permanence:** if at an independently established n the actual `||S^n f0||² < B`, the same strict bound holds for every k≥n. AJI proves n=1 impossible, so any genuine first witness is n≥2.
3. **Eventual-tail characterization:** `||Q f0||² < B` iff there exists N≥2 such that **all** k≥N satisfy `||S^k f0||² < B`. This strengthens the quantifier description of AJI's already proven finite-witness iff, not the unproved strict top-budget comparison.
4. **Finite geometric certificate:** for any actual n>0, the independent premise `||Q f0||² + (||R||^n * ||Q⊥ f0||)² < B` yields the strict original n-th power AJA witness, by AJZ exact Pythagoras and AJI genuine decay upper bound. The numerical premise is NOT certified.
5. **Unconditional weaker variance drop:** there exists some n≥2 with `||S^n f0||² < V-C/2`, via AJV positive q-free correction and AJI strong convergence. This is a genuine finite-power energy reduction but **not** an unconditional AJA witness: no claim `V-C/2<B` is made.

## 3. New declarations audited 8/8

1. `realHilbert_contracting_power_normSq_succ_le_ake`
2. `realHilbert_contracting_power_normSq_antitone_ake`
3. `GroundStatePosteriorJoint.p4Q2PZ37AKE_originalSource_power_energy_antitone`
4. `GroundStatePosteriorJoint.p4Q2PZ37AKE_originalAJA_witness_persists`
5. `GroundStatePosteriorJoint.p4Q2PZ37AKE_originalAJA_exists_iff_eventual_all_power_witnesses`
6. `GroundStatePosteriorJoint.p4Q2PZ37AKE_originalFullTop_small_iff_eventual_all_power_witnesses`
7. `GroundStatePosteriorJoint.p4Q2PZ37AKE_originalExactPower_geometric_square_test`
8. `GroundStatePosteriorJoint.p4Q2PZ37AKE_originalQFree_exists_finite_variance_drop`

## 4. Exact unresolved obstruction — do not promote conditional results

- Genuine unconditional `||Q f0||² < B` for every finite H, beta>0 is **OPEN/NO_DATA**, so genuine unconditional `∃n≥2, ||S^n f0||²<B` is also **OPEN**; neither witness existence nor nonexistence is established.
- Certified AJX says `B≤V/16` and any true AJA witness requires `||Q⊥f0||²>15V/16`; that actual strong angular separation remains unproved.
- Certified AJW rules out the *specific coarse* sufficient comparison `V-C<B`; this is not a no-go theorem for genuine AJA witnesses. Hence the unconditional `V-C/2` threshold above cannot be silently relabelled as B.
- Actual original-Haar full-top vs B evaluation, top dimension one, H-uniform coercivity, Hamiltonian spectral gap and 4D continuum Yang–Mills mass gap remain OPEN.

Append-only / tighten-only / overwrite-forbidden / same-root. No Wilson/Haar/ZW/AJA definitions or hypotheses, old theorems, tooling pins, or other Lean modules were changed. Docs-only manually run Lean is prohibited.
