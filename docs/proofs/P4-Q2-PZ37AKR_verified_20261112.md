# P4-Q2-PZ37AKR — genuine H=14 complement Borel-cell Haar certificates

Date: 2026-11-12 JST. Authoritative theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Original model and research boundary

This AKR leaf does **not** replace the original complete finite SU(2)
Wilson one-slab operator P, its normalized S=P/||P||, the centered ZW
signed physical source f0, the real full-top eigenspace projection Q,
product spatial Haar probability mu_H, genuine normalized continuous
source-transfer representative u_H, AIG negative margin m_H, negative
region E_H={B:u_H(B)<-m_H}, or the strict original AJA budget
B_H=m_H²*mu_H(E_H). The coupling beta0=log(3/2)/64, H=14 and
p_14=81000 are unchanged, as are assumptions, Lean/mathlib pins,
canonical root and the previous AKQ no-witness threshold.

The **actual** original H14 Haar negative-region mass r14 is NO_DATA.
AKR proves a direct, unconditional lower bound r14>=1/2 (from the
existing AIB beta0<=1/128<7, AIT true half-Haar and AIW original
negative-region equality). This is **not** an upper mass bound.

## Five new Lean4 theorems: exact predicates and descent

Source:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH14ComplementBorelCellCertificateV5_PZ37AKR.lean`

1. `real_probability_finite_complement_cells_budget_akr`:
for *any original probability measure*, measurable pairwise-disjoint
Borel cells Ci of the complement E^c, and independently certified
rational lower bounds qi<=mu(Ci), prove
`mu.real(E)+sum_i qi<=1`. No uniform grid or new probability law
is used and no numerical Haar integral is assumed.

2. `p4Q2PZ37AKR_originalH14_negativeHaarMass_ge_half`:
for the genuine H14 original negative region, `1/2<=r14`
with **no extra hypothesis**.

3. `p4Q2PZ37AKR_originalH14_negativeHaarMass_le_of_rationalCells`:
given Borel cells Ci, verified pointwise rational transfer floors
`li<=u14(B)` for all `B in Ci`, with `li>=-m14`, plus
genuine original Haar mass bounds `qi<=mu14(Ci)`, prove
`r14<=1-sum_i qi`. Both the universal pointwise enclosure and
every Haar mass bound remain explicit **proof obligations**.

4. `p4Q2PZ37AKR_originalH14_gaussianHaarTest_of_rationalCells`:
if the certified rational sum is at least the **exact** threshold
`1-4*exp(-beta0²*81000/2)`, prove the genuine AKQ condition
`r14*exp(beta0²*81000/2)<=4`.

5. `p4Q2PZ37AKR_originalH14_no_AJA_witness_of_rationalCells`:
under precisely those actual-cell and threshold hypotheses,
apply unchanged AKQ to exclude the **original** finite-power strict
AJA witness. This does NOT exclude a witness unconditionally.

The decimal reference threshold for complement mass is approximately
0.212791446641. It is **not** a measured r14, nor a certificate for
the total original complement. A finite certified list of valid cells
with sufficient actual Haar mass has **not** been constructed.

## Exact-source Lean4 certification

Theorem PR [#6700](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6700)
merged to canonical formal as squash
`a1184bd3840f39e0753cd096703f397028dbf96a`.
Certified source HEAD:
`a6b2ac20a83c79371a557771920ab2b2b256001e`.

Exact-source GitHub Actions
[CI #43222014058](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43222014058)
completed SUCCESS. Pinned Lean v4.30.0-rc2, pinned mathlib
5450b53e5ddc75d46418fabb605edbf36bd0beb6.
The actual run built 11,454/11,454 dependencies; all 5/5
`#print axioms` checks show only `propext`,
`Classical.choice`, `Quot.sound`, **no sorryAx**.
Changed AKR warning/error 0/0.

Source HEAD, synthetic test-merge and squash commit have the identical
Git tree `7e45dcafe8945d152b588617333be408d57b59ab`.

The first CI failure was the fixed Lean parser's unscoped `on`
notation and quotation of the local set builder; replaced with explicit
`Pairwise (fun i j => Disjoint ...)` and an ordinary lambda for the set.
The second CI failure was attempting to rewrite a set-equality theorem
in an already beta-reduced `MeasurableSet` target. The final proof
rewrites the *original AIG measurability hypothesis* in the reverse
direction and transports it to the original normalized set. No
existing theorem's statement, physical definition or assumption changed.

The independent post-squash formal-branch push
[CI #43223016144](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43223016144)
is separately subject to completion and exact-head checks; this
paragraph does not pre-certify its result.

## Next independent, unresolved numerical task

Construct and validate **actual** finite H14 Borel cells Ci with
nonoverlap, measurable original SU2 spatial Haar masses,
rigorous original Wilson transfer lower intervals on **every**
configuration in each cell, and certified rational mass lower bounds
summing above the exact 0.21279... complement threshold.
Existing AGP, AGU, AGQ signed-Haar and mass-interval structures are
potential inputs, but their noncomputably chosen rational enclosures
are **not** concrete numerically evaluated table entries.
One cell's sign or a floating-point Monte Carlo output cannot
be silently promoted to a full Haar certificate. If no such verified
cells are provided, r14 upper bound and Delta14 sign remain NO_DATA.

No unconditional H14 AJA existence/absence, no H-uniform GL Rayleigh
lower bound, no Hamiltonian spectral gap, and no continuum
four-dimensional Yang--Mills mass gap are claimed.

Append-only / tighten-only / overwrite-forbidden / same-root.
The authoritative Lean theorem belongs on formal; the public main
branch mirrors this exact proof record and appended README/ROADMAP
only after separate CI verification.


## Independent canonical AKR squash push verification — 2026-11-13 JST

The actual, separate canonical formal push workflow
[CI #43223016144](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43223016144)
on exact integrated SHA `a1184bd3840f39e0753cd096703f397028dbf96a`
completed **SUCCESS**. Lean job `131199092171` completed/SUCCESS with
`[11454/11454] Built ...PZ37AKR`; five/ five actual multiline
`#print axioms` results contain only `propext`, `Classical.choice`,
`Quot.sound`, no sorryAx and changed-file error/warning 0/0.
Independent completion receipt job `131202291241` completed/SUCCESS:
`event=push`, exact integrated SHA,
`source_result=success`, published GitHub commit status `success`.
The integrated Git tree is exactly the tested tree
`7e45dcafe8945d152b588617333be408d57b59ab`.
This authenticates the conditional AKR theorem, **not** any actual
H14 upper Haar mass nor unconditional finite-power AJA no-go.
