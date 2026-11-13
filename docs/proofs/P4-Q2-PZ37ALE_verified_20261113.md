# P4-Q2-PZ37ALE — genuine original SU(2) pair-Haar second-moment positive floor

2026-11-13 JST. Authoritative formal proof branch: \`formal/real-hilbert-uniform-coercive-strong-limit\`.
[Lean4 theorem PR #6737](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6737) **MERGED**.

## Scope: exact original model only

One new append-only Lean4 file:
\`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPairHaarSecondMomentPositiveFloorV5_PZ37ALE.lean\`.
No pre-existing Lean source, Wilson SU(2) action/source, full one-slab halfweights,
true product Haar, Gauss-law physical Hilbert transfer, original fixed coupling,
top projection, AJA budget or negative margin, pinned Lean/mathlib, root,
workflow or prior theorem statement was changed.

This proof explicitly keeps separate the *linear* original crossing ACTION
\`C_H(A,B)\` from the original exponential crossing KERNEL
\`Kcross_H(beta,A,B)=exp(-beta*C_H(A,B))\`. The earlier AHR
action-orthogonality theorem is **NOT** promoted to exponential-kernel
orthogonality; the mixed pair-Haar term is evaluated ONLY without
the crossing kernel, exactly where independence holds.

## Certified mathematics and original measured quantities

Let \`ell_H\` be the actual spatial link-list length,
\`V_H=∫ f_H(A)^2 dmu_H(A)>0\` be AHN's original genuine source Haar
second moment, and \`M2pair_H(beta)\` be ALC's original true
crossing-weighted pair-source second moment.

1. The actual Wilson crossing-action global bound, from original
   \`periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_le_two_mul_length\`,
   gives \`C_H(A,B)<=2*ell_H\` at all true SU(2) configurations. Hence
   at beta>=0, the **true** exponential crossing kernel satisfies the
   pointwise \`Kcross_H(beta,A,B) >= k_H(beta):=exp(-2*beta*ell_H)>0\`.
2. AGN and AIW's actual exact spatial Wilson Haar mean prove
   \`∫ f_H(A) dmu_H(A)=0\` for the specified CONTINUOUS original ZW
   source representative; not a made-up pointwise L² representative.
3. Genuine normalized spatial product Haar gives the two marginal
   squares \`∫ f_H(A)^2 d(mu_H×mu_H)=V_H\` and
   \`∫ f_H(B)^2 d(mu_H×mu_H)=V_H\`. Independent unweighted
   Haar crossing \`∫ f_H(A)*f_H(B) d(mu_H×mu_H)=0\`.
   Thus \`∫(f_H(A)+f_H(B))² d(mu_H×mu_H)=2*V_H\` exactly.
4. Integrability and the true pointwise original-kernel floor yield
   **unconditional at every finite H for beta>=0**
   \`M2pair_H(beta)>=2*k_H(beta)*V_H>0\`.
5. Consequently, ALD's physical original transfer norm lower bound is
   \`||P_H(beta)||>=exp(-beta*p_H)*(Zcross_H(beta)+
   (beta²/4)*(2*k_H(beta)*V_H))\`.
   For beta>0 this is a strictly stronger finite-volume floor than
   the old original AIW spatial-mean norm lower bound.
   The exact original H=22, fixed beta0, p22=292008 strict improvement
   is also a separate Lean4 theorem.

This **strict improvement is finite-H**, with an explicitly exponentially
decaying floor in ell_H. There is no certified positive uniform-H
coercivity, no Hamiltonian spectral gap, and no continuum 4D YM mass gap.

## Formal declarations, authentication, and correction provenance

All **15** new public declarations have individual \`#print axioms\`.
The exact-source certified HEAD is
\`9091fd8489b5a2a7a4583b0404a7eb6b89abe73b\`.
Canonical formal theorem squash is
\`958ea765ab503a6bdf02471192a7e60a85973d20\`.
The source HEAD, synthetic PR test merge and integrated squash have
the identical Git tree \`1a9de2ce638756f593bc491518a39b759f956a62\`.

- Initial CI [#43418097047](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43418097047) **FAILURE**: local notation with a projected \`.length\` term lacked quote/precheck support; \`muH.prod\` was not valid with local notation; integration of function-addition without \`Pi.add_apply\` elaboration caused errors.
- First source-only repair \`522e0aec8c868c26e501ac09aaf95ceb03c14b0f\`; CI [#43419061238](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43419061238) **FAILURE**, now only 2 direct Lean errors: nested \`Pi.add\` integral rewriting and \`add_le_add_left\` orientation.
- Second source-only repair \`9091fd8489b5a2a7a4583b0404a7eb6b89abe73b\` explicitly uses \`simp only [Pi.add_apply]\` with independent inner/outer \`integral_add\` witnesses and \`linarith\` for additive inequality.
- Final genuine exact-source [CI #43419944499](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43419944499) **completed/SUCCESS**. Fixed Lean v4.30.0-rc2/mathlib \`5450b53e5ddc75d46418fabb605edbf36bd0beb6\`, genuine dependency closure **11,467/11,467**, public new \`#print axioms\` **15/15** each only \`propext\`, \`Classical.choice\`, \`Quot.sound\`, no new \`sorryAx\` and changed ALE warning/error **0/0**. Changed-Lean job \`131867136265\` completed SUCCESS.
- Independent exact-source receipt job \`131869759629\` completed SUCCESS and logged
  \`[mcp-receipt] event=pull_request exact_sha=9091fd8489b5a2a7a4583b0404a7eb6b89abe73b source_result=success run=43419944499 attempt=1\`.

## Formal independent push: initial pending observation

Canonical formal push [CI #43420956000](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43420956000)
for exact squash HEAD \`958ea765ab503a6bdf02471192a7e60a85973d20\`
was initially **in_progress**. The final status, independent push receipt
and precise post-merge audit are PENDING in this historical snapshot.
Append independently observed evidence without deleting the earlier state.

## Open obstructions and next original-model task

The original H22 negative-region Haar upper mass
\`r22<=4*exp(-(44/351)*beta0²*292008)\` (~0.920418) is **NOT proved**.
True H22 complementary Haar-cell lower mass and any unconditional
AJA witness nonexistence are still NO_DATA. AKZ proves the *old AKX*
sufficient scalar premise fails for all H>=25, but no AJA witness
existence follows. The new ALE norm lower bound does not by itself
resolve AKX's physical Haar/top budget comparison.

NEXT: compare the certified strictly improved original norm lower bound
with the **true** original negative-margin/Haar budget and full-top
projection at H22, without confusing a sufficient test's failure with
a witness. Separately seek concrete positive-side H22 Haar-cell
certificates. Preserve explicit H dependence and all unresolved gaps.

Append-only / tighten-only / overwrite-forbidden / same-root.
