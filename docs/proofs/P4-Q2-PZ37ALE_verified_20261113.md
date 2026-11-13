# P4-Q2-PZ37ALE — genuine SU(2) pair-Haar second moment positive floor

2026-11-13 JST. Authoritative research branch: `formal/real-hilbert-uniform-coercive-strong-limit`.

[Theorem PR #6737](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6737) is **MERGED**. The original Wilson SU(2) spatial/crossing/full one-slab kernels, normalized spatial product Haar, Gauss-law ZW source and physical transfer, AJA strict event and budget, top projection, fixed beta0, pinned Lean/mathlib and formal root are unchanged. Exactly one new append-only Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPairHaarSecondMomentPositiveFloorV5_PZ37ALE.lean` (357 lines at certified HEAD; 15 declarations and matching 15 `#print axioms`).

## Certified original-model mathematical content

Let `ell_H` be the exact original finite spatial link count, `f_H` the same original centered continuous Gauss-law source, `V_H=∫ f_H(A)^2 dmu_H(A)` the original AHN source second Haar moment, and `Kcross_H(beta,A,B)=exp(-beta*Ccross_H(A,B))` the **actual** original temporal crossing kernel. For `beta>=0`:

1. The pre-existing crossing **ACTION** bound `Ccross_H(A,B) <= 2*ell_H` rigorously yields the original exponential crossing **KERNEL** floor `Kcross_H(beta,A,B) >= exp(-2*beta*ell_H)>0`.
2. The true continuous original source has zero original spatial normalized Haar mean, using AGN's pointwise centered-action identity and AIW's genuine Wilson mean.
3. Genuine independent two-endpoint original product-Haar Fubini identifies each marginal source-square integral with `V_H`, the *unweighted* mixed source integral with zero, and
   `∫ (f_H(A)+f_H(B))^2 d(mu_H×mu_H) = 2*V_H`.
4. The original crossing-*weighted* second moment then satisfies the unconditional finite-volume lower bound
   `M2pair_H(beta) >= 2*exp(-2*beta*ell_H)*V_H > 0`, since AHN has already certified `V_H>0`.
5. Combining ALE with the unchanged true full-Wilson physical norm estimate of ALD,
   `||P_H(beta)|| >= exp(-beta*p_H)*[Zcross_H(beta) + (beta^2/4)*2*exp(-2*beta*ell_H)*V_H]`.
   At each finite H and `beta>0` the original operator norm is **strictly** above AIW's `exp(-beta*p_H)*Zcross_H(beta)` floor. The actual H=22, beta0=log(3/2)/64 and p22=292008 specialization is certified.

**Compatibility:** The vanishing mixed term is for **unweighted product-Haar** only. The crossing-weighted mixed integral is not set to zero. AHR's orthogonality against the original linear crossing ACTION is not illegitimately promoted to the exponential crossing KERNEL.

## Exact-source Lean4 error/repair history

Initial original ALE source `ae865c61875e306a594615b5408ad30907dede16` failed [CI #43418097047](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43418097047). The actual file produced 16 direct Lean errors (including invalid dotted projection syntax within `ellH`, unelaborated notation, attempted `muH.prod` on a local notation instead of `Measure.prod muH muH`, and dependent rewriting/function-addition normalization). This failed source did **not** have a clean new-axiom audit; its `sorryAx` printouts must not be treated as certified.

Intermediate revised source `522e0aec8c868c26e501ac09aaf95ceb03c14b0f` failed [CI #43419061238](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43419061238) with two residual Lean elaboration errors (unmatched rewrite and type mismatch). These failed attempts remain part of the repair provenance; they are not overwritten as successes.

Final certified source `9091fd8489b5a2a7a4583b0404a7eb6b89abe73b` passed [exact-source PR CI #43419944499](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43419944499), completed **SUCCESS**, pinned Lean v4.30.0-rc2 and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`: dependency closure **11,467/11,467**; 15/15 actual new `#print axioms` use **only** `propext`, `Classical.choice`, `Quot.sound`; no new `sorryAx` and changed ALE warning/error 0/0. Changed-Lean job `131867136265` completed SUCCESS, independent exact-head completion receipt job `131869759629` completed SUCCESS with the observed line:

`[mcp-receipt] event=pull_request exact_sha=9091fd8489b5a2a7a4583b0404a7eb6b89abe73b source_result=success run=43419944499 attempt=1`.

Canonical formal theorem squash is `958ea765ab503a6bdf02471192a7e60a85973d20`. Independently retrieved Git commit objects confirm the **same source/squash Git tree** `1a9de2ce638756f593bc491518a39b759f956a62`.

The separate [canonical formal push CI #43420956000](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43420956000) for exact formal squash HEAD `958ea765ab503a6bdf02471192a7e60a85973d20` also completed **SUCCESS**. Actual changed-Lean job `131870517081` certified **11,467/11,467**, 15/15 standard-three axiom outputs, no ALE warning/error; independent completion receipt job `131872606567` completed SUCCESS and logged:

`[mcp-receipt] event=push exact_sha=958ea765ab503a6bdf02471192a7e60a85973d20 source_result=success run=43420956000 attempt=1`.

## Open physical obstructions and next work

The finite-H floor is `exp(-2*beta*ell_H)` and decays as volume grows. It **does not** certify a positive H-uniform coercivity constant, a Hamiltonian or continuum gap, or any analogue of a continuum Yang–Mills mass-gap theorem.

The H22 original genuinely negative Haar mass `r22` is still **NO_DATA** above, and AKX's sufficient hypothesis `r22 <= 4*exp(-(44/351)*beta0^2*292008)` remains unproved. Existing AKZ independently proves the **old AKX sufficient criterion is impossible for H>=25**, which says nothing by itself about existence of AJA witnesses or other sufficient criteria.

A next legitimate proof stage is to combine ALE's explicit positive norm-floor improvement with existing original top/AJA budget inequalities, accounting for all normalization and monotonicity directions before proposing a *new* sufficient test. Alternatively construct truly measured H22 complementary Borel-cell floors under AKY. Do not upgrade an observed local moment improvement to an AJA verdict without a verified comparison and descent.

Operating policy: append-only / tighten-only / overwrite-forbidden / same-root.
