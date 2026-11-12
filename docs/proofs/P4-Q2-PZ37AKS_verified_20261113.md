# P4-Q2-PZ37AKS — unconditional original H=14 AJA finite-power no-witness

Date: 2026-11-13 JST. Authoritative theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.
This is a new, machine-verified analytic tightening; no original
SU(2) Wilson model, Haar probability, coupling, source, or AJA
strict-budget definition has been replaced.

## Mathematical result and precise scope

Use the unchanged original fixed coupling
`beta0=log(3/2)/64`, original H14 plaquette count
`p_14=81000`, Wilson spatial Haar probability `mu_14`,
original signed ZW physical source `f0`, normalized original
one-slab transfer `S=P/||P||`, original normalized continuous
transfer representative `u`, AIG original negative margin `m`
and true strict budget `B=m²*mu_14{u<-m}`.

AKP previously proved the *particular loose scalar sufficient test*
`beta0²*p_H/2<=log 4 iff H<=13`. AKP does NOT assert that a
finite-power AJA witness exists for H>=14. AKS retains AKP's theorem
and proves a genuinely sharper sufficient no-witness criterion.

Existing true SU(2) normalized Haar character chi=1-E has:
- `E_Haar chi=0` from AIQ/PZ35D4;
- `E_Haar chi²=1/4` from the exact ACK four-mode SU(2) Haar Gram;
- pointwise `|chi|<=1` from AIQ.

The pinned mathlib exact quadratic Taylor remainder
`|exp(x)-1-x|<=x²` for `|x|<=1` gives, for `0<=beta<=1`:

```text
mgf_chi(beta) <= 1 + beta²/4 <= exp(beta²/4)
z_original(beta) <= exp(-beta+beta²/4)
Zcross_H_original(beta) <= exp(p_H*(-beta+beta²/4)).
```

No fictitious Gaussian law or plaquette independence is assumed.
The exact original AIF product partition is used, and the
original SU(2) Haar expectation is unchanged.

Existing AKO rational analytic bounds prove
`0<beta0<=1/156` and `11/8<=log4`; together with
`p14=81000`, AKS proves

```text
beta0²*81000/4 <= 11/8 <= log4.
Zcross_14(beta0) <= 4*exp(-beta0*p14).
```

Since the **genuine original** Haar probability obeys
`r14=mu_14{u<-m}<=1` (regardless of its unknown value), AKS
certifies AKQ's ORIGINAL partition-Haar test:

```text
r14 * Zcross_14(beta0) <= 4*exp(-beta0*p14).
```

Via the already-verified AKQ non-witness theorem this proves, without
a new mass assumption:

```text
not exists (n : Nat), || S_14(beta0)^n f0_14 ||² < B_14(beta0).
```

A further theorem combines AKO (H<=13) with AKS (H=14) to certify
the same **strict original AJA finite-power witness nonexistence
for EVERY H<=14**.

The actual numerical H14 negative Haar mass `r14` remains
**NO_DATA**; AKR's lower `r14>=1/2` remains true.
No new upper bound on `r14`, no sign certification of
`Delta14=B14-||Qf0||²`, and no H-uniform GL Rayleigh,
Hamiltonian spectral gap or continuum four-dimensional Yang--Mills
mass gap are claimed.

## Exact Lean4 declarations and machine verification

New single file:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH14ExactCharacterMomentAJANoGoV5_PZ37AKS.lean`

Nine audited declarations:
1. real_exp_le_one_add_sq_of_abs_le_one_aks
2. originalSingleLinkCharacter_secondMoment
3. originalSingleLinkCharacter_mgf_le_quarter
4. originalSingleLinkPartition_le_quarterGaussian
5. originalCrossingPartition_le_quarterGaussian
6. originalH14_fixedCoupling_quarterBudget_le_logFour
7. originalH14_partitionHaarMass_unconditional
8. originalH14_no_AJA_finitePower_witness
9. originalFixedCoupling_le_fourteen_no_AJA_power_witness

All latter eight declarations are in namespace
`MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`.
The first is in `MGAP4D.MathlibAnalytic`.

[AKS theorem PR #6703](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6703)
MERGED to canonical formal squash
`0481923e78a323faf04c6efc1c77dd402ec3bb3c`.

Exact-source certified HEAD:
`cba7df900ed607959531c01905e68a125705ee34`.

[Exact-source CI #43309954309](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43309954309)
**completed/SUCCESS**. The real Lean dependency closure was
11,454/11,454 SUCCESS. All nine multiline `#print axioms`
audits depend solely on `propext`, `Classical.choice`,
`Quot.sound`, with **no sorryAx**, changed AKS warning/error 0/0.
Independent CI completion receipt job `131506034153`
completed/SUCCESS: `event=pull_request`, exact certified HEAD,
`source_result=success`, published GitHub status success.

Source, synthetic test-merge and canonical squash share exactly
Git tree `3b45ae6a224dbc81293c10b37a985c31d151cb83`.

First two initial Lean4 check attempts failed at the integration
`integral_add` proof because the pinned elaborator could not match
an already beta-reduced lambda expression with pointwise function
addition under a rewrite tactic. The final source explicitly
constructs Haar integrals of constant, linear and quadratic terms,
then uses the typed `integral_add` equalities directly.
All original physical definitions, theorem statements, assumptions
and pinned toolchain remain unchanged.

Independent actual canonical formal squash push
[CI #43311024308](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43311024308)
is checked separately; this paragraph does not pre-certify its
completion.

## Open research boundary

AKS proves the true H14 finite-power no-witness by a new
analytic partition bound; it does NOT determine the actual Haar
negative-region mass or Delta14 sign.
The AKR finite Borel complementary-cell mass certification remains
a separate unresolved **numerical** task. Extension above H14
requires new exact scalar/Haar quantitative proofs before claims
for any H>=15; no global mass-gap conclusion follows.

Append-only / tighten-only / overwrite-forbidden / same-root.
The authoritative Lean theorem is on formal and any public main
mirror uses an identical proof-record blob, with no Lean transfer.
