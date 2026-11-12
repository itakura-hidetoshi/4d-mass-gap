# P4-Q2-PZ37AKJ — original Ward-character no-witness extension above logarithmic cutoff

2026-11-12 JST. Explanatory proof receipt. Lean theorem authority resides solely on canonical `formal/real-hilbert-uniform-coercive-strong-limit`, not in this prose.

## Exact-source mechanical certification

- [PR #6676](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6676) MERGED. Final source `da6af5ec53855742570e5caeb2bc1f5dc635ff32`, formal squash `2403229c6db3ba3e7702cc014a875fa9f91493d6`, source/test-merge/squash identical Git tree `6b66c5c07a090d46309cd68b1b1e17c48c5fcb11`; new leaf blob `6bd2cc44231b97cc028da96ea4387a8da45ef065`.
- [Exact-source CI #43153265889](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43153265889) completed/SUCCESS: workflow, changed-Lean job/step, independent exact-head completion receipt. 11,448/11,448 Lean dependency closure, nine of nine audited declarations use only `propext`, `Classical.choice`, `Quot.sound`; changed warning/error 0/0; forbidden sorry/admit/axiom 0. Full diagnostic artifact `13914379798`; checked its complete 2,078,695-byte `lean-fast.log`, SHA256 `285ceb4b4e81dc97b119cc9d43ef8c6e5ce8c3bca796c75e18fd92305eec2d88`.
- Initial CI #43152503698 failed on Lean positivity/closed goals and unused names; fixes only the new AKJ leaf, not a source/hypothesis/model rewrite.
- Independent formal push CI [#43154080548](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43154080548) is a separate audit gate. Its final status is NOT claimed by this initial record.

## Mathematical scope (actual original model)

Let `p_H` be the original plaquette count, `r(beta)>0` the original ABN continuous temporal character coefficient, `S=P/||P||` the genuine Wilson transfer and `f0` the original centered signed ZW source. Define an auxiliary *criterion* without replacing any old data:

```text
D_H(beta) = 2*exp(-2*beta*p_H) + exp(-beta*p_H)*r(beta)^4.
```

The new kernel-checked conditional statement is:

```text
beta>0 AND D_H(beta)>=1
=> forall n:Nat, ||S_H,beta^n f0,H||^2 >= B_H,beta
=> no strict ORIGINAL finite-power AJA witness.
```

At `kappa_H=log 2/(2p_H)`, `D_H(kappa_H)>1` because `r(kappa_H)>0`; `D_H` is continuous by already verified ABN. Thus for every original finite H, there **exists a genuine beta>kappa_H** with no strict AJA witness. This is a strict logical extension beyond AKI's range, not merely an abstract countermodel. It does **not** decide every beta>kappa_H or establish the absence/presence of a physical mass gap.

The positive Ward affine coefficient c is retained in the true top pairing; no top rank-one hypothesis, original Wilson/Haar/ZW/AJA change, weakening, sorry/admit/axiom, or pinned Lean/mathlib change.


## Subsequent independent formal-push confirmation (2026-11-12)

The earlier pending-state entry remains as the historical observation. Independently re-observed [formal push run #43154080548](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43154080548) is now **completed/SUCCESS** at exact formal squash `2403229c6db3ba3e7702cc014a875fa9f91493d6`, attempt 1. Actual [Changed Lean job #130969835468](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43154080548/job/130969835468), its `Run changed Lean fast check` step 17, and separate [completion-receipt job #130972144127](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43154080548/job/130972144127) all completed/SUCCESS. The receipt log identifies that exact squash SHA and `source_result=success`; the corresponding commit-status receipt is success.

The complete decoded push-job log reports **11,448/11,448** and `Build completed successfully (11448 jobs)`. All nine AKJ axiom outputs contain only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` occurs, the forbidden-token audit passed, and changed AKJ warning/error counts are **0/0**. Independent source [run #43153265889](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43153265889), actual Lean job `130967215988` and exact-source receipt job `130969569983` were also re-observed completed/SUCCESS with the same closure and axiom results. Its checkout log identifies actual test-merge `48cea85d86cbc4e16a50f9b49a3b792787364e66`. Re-reading the Git commit objects confirms source `da6af5ec53855742570e5caeb2bc1f5dc635ff32`, that test-merge, and formal squash all have tree `6b66c5c07a090d46309cd68b1b1e17c48c5fcb11`; the AKJ leaf remains blob `6bd2cc44231b97cc028da96ea4387a8da45ef065`.

The prior artifact byte-count and extracted-log SHA256 remain the earlier recorded audit; this confirmation independently checked the complete decoded GitHub job logs and current artifact metadata. These receipts certify the stated finite-H theorem scope only. No additional coupling-wide, top-simplicity, uniform-coercivity, Hamiltonian or continuum-gap conclusion is added.
