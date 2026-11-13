# P4-Q2-PZ37ALA — genuine SU(2) diagonal center-twist crossing Haar descent

2026-11-13 JST. Authoritative proof branch `formal/real-hilbert-uniform-coercive-strong-limit`.
The original physical Wilson SU(2) one-slab transfer, Gauss-law source, product Haar,
negative AJA margin, full-top projection, original fixed beta0 and all dependency
pins remain unchanged. This is a **new exact symmetry bridge**, not an H22 numerical Haar result.

## Genuine original identities

Let `T_H` be the already certified even-periodic center-cochain spatial twist
constructed in AHW, and `f_H` the unchanged centered ZW continuous source.
AHW2 already proves `f_H(T_H A)=-f_H(A)` and
`W_H(T_H A)=2*p_H-W_H(A)`.

ALA proves **nine** new public Lean declarations:
1. Central cancellation `((a*s)⁻¹*(b*s))=a⁻¹*b`, with original SU(2) center sign.
2. Unchanged genuine one-link original Wilson relative factor under the same translate.
3. Unchanged genuine all-link original crossing kernel `Kcross(T_H A,T_H B)=Kcross(A,B)`.
4. Paired unchanged original centered source sum is odd.
5. Squared paired original centered source sum is even.
6. Original spatial halfweight dual formula:
   `exp(-beta*W(TA)/2)=exp(-beta*p_H)*exp(beta*W(A)/2)`.
7. Genuine product original Haar measure is **measure preserving** under the
   diagonal pair map `Prod.map T_H T_H`, established from the actual individual
   Haar-preserving spatial center twists via `MeasurePreserving.prod`.
8. Crossing-weighted two-boundary original source is odd.
9. Crossing-weighted squared two-boundary original source is even.

These are true global two-boundary geometric and measure statements.
They do **not** themselves establish an exponential Haar integral, a
quantitative positive quadratic correction, the source variance scale in p_H,
an H22 r22 upper mass, unconditional H22 AJA no-witness, physical
Hamiltonian gap or continuum four-dimensional mass gap. The proper
descent from local identities to a new norm estimate remains a next theorem.

## Exact-source authentication

[Theorem PR #6727](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6727) MERGED.
Initial six-declaration source `22311369581ac23dfb98118ba7ae153600bd382b`
passed [CI #43381545846](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43381545846).
The **final superseding** nine-declaration exact-source commit is
`c684da81d1ab7ac14dea73d26b9791821b2e1853`,
canonical squash `7134b92179196b40b0e454060b4ef77e69bb0be3`,
common original source/test-merge/squash tree
`4a32fbc9e9cf7f55d70f2d60126b63c5da647fdd`.

[Exact-source CI #43382294445](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43382294445)
completed SUCCESS, Lean dependency closure **11,463/11,463**, actual
9/9 `#print axioms` all only `propext`, `Classical.choice`,
`Quot.sound`, no new sorryAx, changed ALA warning/error 0/0.
Changed-Lean job `131742642716` completed SUCCESS; independent
exact-head completion receipt job `131744372027` completed SUCCESS:
```
[mcp-receipt] event=pull_request exact_sha=c684da81d1ab7ac14dea73d26b9791821b2e1853 source_result=success run=43382294445 attempt=1
```
Published commit status success.

Independent canonical formal squash [push CI #43382985587](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43382985587)
must be independently checked for completed SUCCESS, exact-head receipt,
nine public standard-only axiom outputs and the same canonical Git tree
**before** its receipt is appended and the formal proof record is merged.
This sentence records the initial pending state, not an anticipated success.

## Remaining original-model tasks

The next intended transformation is genuine pair-Haar cosh symmetrization:
prove `integral Kcross*exp(-beta*(fA+fB))` equals its even average
using the actual MeasurePreserving property, then rigorously bound its
second/fourth source moment and derive a stronger original physical
`lambda_H` lower bound. For H=22 the truly required original r22
upper bound or alternate sufficient norm/top estimate is still NO_DATA.
AKX is proved incompatible for H>=25, but its failure does not
imply any original AJA witness. Preserve all obstructions.
Append-only / tighten-only / overwrite-forbidden / same-root.


## Independent authoritative canonical formal-push verification (2026-11-13 JST)

The earlier pending-status description is preserved as the initial draft snapshot. ALA canonical squash `7134b92179196b40b0e454060b4ef77e69bb0be3` independently passed genuine [formal push CI #43382985587](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43382985587), completed/**SUCCESS**, pinned Lean **11,463/11,463**, all 9/9 new ALA actual `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`, sorryAx none, ALA changed warning/error **0/0**. Main Lean job `131744850974` completed SUCCESS and exact-head completion receipt job `131746833019` completed SUCCESS, with actual `[mcp-receipt] event=push exact_sha=7134b92179196b40b0e454060b4ef77e69bb0be3 source_result=success run=43382985587 attempt=1`; published GitHub commit status SUCCESS. The integrated tree `4a32fbc9e9cf7f55d70f2d60126b63c5da647fdd` matches certified source and test-merge. It still does not numerically bound r22 or prove a new AJA no-witness.
