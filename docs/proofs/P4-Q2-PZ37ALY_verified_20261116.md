# P4-Q2-PZ37ALY — authenticated scaled original-beta0 Wilson raw/full two-volume budget

2026-11-16 JST. [Theorem PR #6767](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6767) **MERGED**, canonical formal commit \`c951f4f669b7f50226303ba2fd7e634270153382\`.

## Exact original physics and conditional theorem scope

One NEW append-only Lean4 leaf (328 added lines, **15/15** independently audited declarations):

\`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0ScaledRawFullNormStepBudgetV5_PZ37ALY.lean\`

The unmodified true SU(2) Wilson physical one-slab norm \`p_H=||P_H||>0\`, genuine full-top-orthogonal raw excitation norm \`a_H=||A_H||\`, normalized \`r_H=||R_H||\` and \`Q_H=r_H²\` refer to fixed \`beta0=log(3/2)/64\`. ALX certifies the exact same-volume identity \`a_H=p_H*r_H\`. The operators at distinct H act on different Hilbert spaces; ALY compares only real scalar norm values.

Assume **independently proved physical** real norm estimates for every adjacent H:

\`\`\`text
eta_H>=0, xi_H>=0, 0<s_H*p_H-xi_H,
a_(H+1)<=s_H*a_H+eta_H,
p_(H+1)>=s_H*p_H-xi_H.
\`\`\`

The common volume-scale is *not* a modification of the true physical model. With \`t_H=(eta_H+xi_H)/(s_H*p_H-xi_H)>=0\`, ALY proves

\`\`\`text
r_(H+1)<=r_H+t_H;
Q_(H+1)<=Q_H+(2*t_H+t_H²);
L_H<=2*t_H+t_H².
\`\`\`

If all partial sums \`sum_{i<H}(2*t_i+t_i²)<=B<delta_0\` are **independently proved**, ALU/ALV imply a positive finite-volume all-H transfer gap at original beta0. A geometric loss budget is also available. Neither the physical estimates nor the summability margin is established in ALY; these are exact **conditional sufficient criteria**, not the physical gap.

## Lean repair and source certification

- Initial source \`fa8ad03...\` introduced one new leaf. Later source \`2997a6592dbd1e95356d6833ef53b072badc6a98\` replaced an opaque generic nonlinear tactic with explicit arithmetic.
- Earlier CI [#43665027590](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43665027590) was CANCELLED after source change; [#43665639036](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43665639036) FAILED at line 116: \`norm_nonneg _\` left \`SeminormedAddGroup ?m.7\` unresolved. That source's derived \`sorryAx\` outputs are NOT certificates.
- Final proof-only repair \`3ecdfd60aa339f8fc463708d8ad24c1298f5c504\` explicitly passes the **actual physical normalized orthogonal transfer operator** to \`norm_nonneg\`, with unchanged theorem statements, hypotheses, physics, roots and pins.
- Final Git source blob: \`fca76367733adf8fd4e4941e357002fe153daf6c\`.
- [Exact-source PR CI #43676401197](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43676401197) **completed/SUCCESS**: pinned Lean **11,489/11,489**, all **15/15** public ALY \`#print axioms\` only \`propext\`, \`Classical.choice\`, \`Quot.sound\`; no \`sorryAx\` and no changed ALY warning/error. Exact-source independent receipt job \`132698594192\` succeeded.
- Source/test-merge/canonical ALY tree: \`b0850c10e8a17dd14ba77be3056b1ebdb261e54f\`. Canonical merge \`c951f4f669b7f50226303ba2fd7e634270153382\`.
- The standalone ALY formal push run [#43693028187](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43693028187) was **CANCELLED**, not certified: it was superseded by the subsequent ALZ integration using the same branch concurrency group. Preserve this non-success provenance.

## Independent canonical ALY+ALZ proof closure

After ALZ [#6768](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6768) MERGED, authoritative formal HEAD \`4e0f4d894dfab5f4ebc426b946052db825ca6c6d\` passed the **separate** [event=push CI #43693765510](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43693765510) **completed/SUCCESS**. Pinned Lean full dependency closure **11,490/11,490**, **ALY 15/15 + ALZ 7/7** public axiom audits standard-three-only, no new \`sorryAx\` or ALY/ALZ warning/error. Lean job \`132750063860\` and independent receipt job \`132783704522\` both SUCCESS.

\`\`\`text
[mcp-receipt] event=push exact_sha=4e0f4d894dfab5f4ebc426b946052db825ca6c6d source_result=success run=43693765510 attempt=1
\`\`\`

The actual canonical ALZ tree \`1f3227d815b37d39909d0a509c1092ae0f74bc3c\` equals its source and synthetic test-merge tree. This certifies the **combined conditional Lean proofs**, not independently missing Wilson physical cross-volume norm estimates.

**NO_DATA / OPEN:** true original SU(2) fixed-beta0 estimates on \`a_(H+1)\`, \`p_(H+1)\`, summable positive margin, all-H physical beta0 transfer gap, Hamiltonian gap, and continuum 4D Yang–Mills mass gap. Never infer them from the successful conditional formal proof.
