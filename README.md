# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository contains a large finite-volume Wilson / Osterwalder--Schrader / physical-transfer development together with the quantitative response, covariance, conditional-expectation, and Hilbert-space infrastructure intended to support a later uniform finite-volume gap and continuum construction.

## Current status — 2026-09-23 JST

The authoritative theorem-carrier branch is

`formal/real-hilbert-uniform-coercive-strong-limit`.

The theorem-bearing baseline immediately before this documentation refresh is

`245d422bef931e769434e2e8607c3d465b9e639b`,

the merge commit of [PR #4656](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/4656), **Identify exact beta-zero ground-state laws with Haar product laws**.

The default branch `main` is a public landing/documentation branch and is **not** theorem authority.

Fresh GitHub state always outranks this document. A later docs-only merge may advance the theorem-carrier branch pointer without changing the mathematical baseline described above.

> **Claim boundary.**
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
> What is now integrated is a substantial finite-volume physical Wilson spine, including a canonical high-temperature strict physical sweep contraction and an exact beta-zero product-Haar / rank-one endpoint. The remaining central finite-volume obligation is a genuine L2 Poincare / Rayleigh estimate connecting the physical interdependence bounds to the ground-state conditional-expectation family. A uniform finite-volume transfer/Hamiltonian gap and the thermodynamic/continuum Yang--Mills construction remain downstream obligations.

## Repository authority

| Item | Authoritative value for this refresh |
| --- | --- |
| Theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Theorem-bearing baseline before this docs refresh | `245d422bef931e769434e2e8607c3d465b9e639b` |
| Latest integrated theorem PR | #4656 — beta-zero vacuum and joint laws are exactly Haar / pair Haar |
| Latest validated theorem head | `fd209bdf7d32b7658d96db018ee7984f6f9621c0` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Default branch | `main` — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean artifacts;
3. README / ROADMAP;
4. CI receipts;
5. historical summaries or memory.

## Proof spine at a glance

```text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT
  -> periodic SU(N) Wilson one-slab kernel
  -> OS / Gauss-law physical carriers
  -> physical transfer operator and top sector
  -> ground-state transformed joint probability law
  -> genuine one-link conditional expectations

CANONICAL RESPONSE / HIGH-TEMPERATURE SPINE                 #4634-#4648
  -> literal fixed-right response continuity
  -> canonical compact-supremum / half-barrier closure
  -> actual physical weighted influence
  -> influence finite resolvent
  -> random-scan contraction
  -> covariance finite resolvent
  -> spatial random-scan resolvent
  -> actual spatial covariance clustering
  -> two-step terminal covariance decay
  -> cubic shell summability
  -> uniform physical remote residual
  -> oscillation sharpening vanishing at beta = 0
  -> positive strict-sweep cutoff
  -> volume-independent strict physical full-sweep contraction

GROUND-STATE L2 RECEIVER                                    #4650-#4652
  -> six-spatial residual energy on genuine joint L2
  -> bounded-concrete-core density closure
  -> genuine six-spatial random-scan Rayleigh receiver
  -> frame/Poincare <-> Rayleigh contraction identity
  -> transfer-gap receiver 3(1-q)/8
  -> abstract finite tensorization for commuting Hilbert projections

EXACT BETA-ZERO ENDPOINT                                    #4653-#4656
  -> ambient one-slab transfer = |1><1|
  -> physical Gauss-law transfer = |1><1|
  -> canonical nonnegative top vacuum = physical constant-one vector
  -> beta-zero vacuum measure = spatial Haar
  -> beta-zero ground-state joint measure = pair Haar

CURRENT FRONTIER
  -> specialize #4652 commuting-projection tensorization to the
     beta-zero genuine six-spatial ground-state conditional expectations
  -> identify the corresponding common-fixed / centered sector exactly
  -> obtain an explicit beta-zero six-spatial frame / Rayleigh contraction
  -> feed #4651 to the physical transfer-gap receiver

NEXT QUANTITATIVE STEP
  -> extend the beta-zero L2 estimate to a volume-uniform positive-beta
     high-temperature regime using the already-integrated physical
     interdependence / conditional-law control
  -> obtain a uniform finite-volume physical transfer/Hamiltonian gap

DOWNSTREAM
  -> compatible thermodynamic limit
  -> continuum OS physical construction
  -> Wightman reconstruction / spectral interpretation
  -> continuum Yang--Mills mass-gap theorem
```

## 1. Canonical high-temperature physical contraction is now integrated

The old documentation stopped at the continuity of the literal fixed-right response (#4634). That is no longer the active frontier.

The canonical chain now continues through the actual physical influence and covariance machinery:

| PR | Integrated result |
| --- | --- |
| #4634 | Joint continuity of the literal fixed-right target-ratio response. |
| #4637 | Canonical half-barrier closure. |
| #4638 | Actual high-temperature physical weighted influence and response decay. |
| #4639 | Weighted finite influence-path / resolvent propagation. |
| #4640 | Canonical finite-volume random-scan contraction. |
| #4641 | Canonical covariance finite-resolvent bound. |
| #4642 | Spatial decay of the finite random-scan resolvent. |
| #4643 | Actual spatial covariance clustering. |
| #4644 | Concrete two-step terminal covariance spatial decay. |
| #4645 | Volume- and background-uniform remote residual bound. |
| #4646 | Oscillation-sharpened terminal covariance prefactor vanishing at beta zero. |
| #4647 | Oscillation-sharpened remote residual vanishing at beta zero. |
| #4648 | Strict physical sweep contraction on a positive canonical high-temperature interval. |

For (s>1), the concrete terminal covariance estimate has base-L1 decay ratio

[
s^{-1}<1.
]

The oscillation-sharpened local amplitudes use the exact intervals already proved in the model:

[
e^{-2eta}le rle e^{2eta},
qquad
e^{-16eta}le Rle e^{16eta},
]

so the sharpened terminal covariance prefactor contains

[
igl(e^{2eta}-e^{-2eta}igr)
igl(e^{16eta}-e^{-16eta}igr),
]

and therefore vanishes exactly at (eta=0).

The sharpened remote residual is inserted into the existing uniform envelope coefficient

[
c_{m env}(eta,ho)
=
18,eta(eta)+ho.
]

PR #4648 proves continuity at zero and constructs a strictly positive cutoff, contained in the canonical half-barrier interval, on which

[
c_{m env}(eta,ho_{m osc}(s,eta))<1.
]

Consequences already integrated:

- strict maximum-column contraction for every finite volume and background;
- volume-independent exponential contraction after a complete physical random-scan sweep.

This is a genuine physical finite-volume contraction result. It is **not** silently promoted to an L2 Poincare inequality.

## 2. The remaining L2 obligation is explicit

PRs #4650 and #4651 isolate the exact Hilbert-space receiver.

The genuine ground-state joint carrier has six actual right-boundary spatial conditional-expectation projections. Their normalized residual energy is now defined directly on the full joint L2 space, and any quantitative estimate proved first on the already-dense bounded concrete core extends to the full carrier with no loss of coefficient.

PR #4651 defines the genuine six-spatial random-scan operator

[
P_{m rs}
=
rac1{6}sum_{c=1}^{6} P_c
]

and proves that, because the (P_c) are self-adjoint idempotents,

[
langle P_{m rs}x,xangle
=
rac1{6}sum_c |P_cx|^2.
]

Hence the six-spatial frame / Poincare estimate

[
kappa|x|^2
le
rac1{6}sum_c |x-P_cx|^2
]

is exactly equivalent to the Rayleigh contraction

[
langle P_{m rs}x,xangle
le
(1-kappa)|x|^2.
]

The existing physical transfer receiver then gives

[
rac{3(1-q)}8
le
	ext{physical top-eigenspace transfer gap}
]

from any six-spatial Rayleigh factor (qle1), and gives a positive transfer gap when (q<1).

This means the finite-volume mass-gap route no longer has an ambiguous “Poincare step”: the exact missing theorem is the construction of a strict L2 Rayleigh/frame estimate for the genuine ground-state conditional-expectation family.

## 3. Abstract commuting-projection tensorization is proved

PR #4652 proves the real-Hilbert theorem needed at the decoupled endpoint.

For a finite family of pairwise commuting self-adjoint idempotent projections, an ordered full sweep satisfies the exact tensorization estimate

[
|x-P_{m sweep}x|^2
le
sum_c |x-P_cx|^2.
]

The proof is abstract and independent of the Wilson model. It proves:

- every self-adjoint idempotent is norm-contracting;
- commuting projections commute through finite sweeps;
- coordinate defects do not increase along the sweep;
- one-step Pythagorean decomposition;
- finite-list and finite-type full-sweep tensorization.

The intended model specialization is now justified by the exact beta-zero product law proved after it.

## 4. Exact beta-zero transfer and vacuum are now canonical

PRs #4653-#4656 close the complete decoupled endpoint normalization.

### Ambient transfer

At (eta=0), the literal temporal-gauge one-slab Wilson kernel is exactly the constant function (1).

Let (1_{m Haar}) denote the normalized constant-one spatial Haar L2 vector. PR #4653 proves

[
K_0
=
1_{m Haar}oxtimes1_{m Haar}
]

as the product-Haar L2 kernel and therefore

[
T_0
=
|1_{m Haar}anglelangle1_{m Haar}|.
]

### Physical Gauss-law transfer

PR #4654 transports the rank-one identity to the genuine physical Gauss-law subspace. The canonical physical constant-one unit vector is fixed, the physical beta-zero transfer has norm exactly one, and the normalized physical transfer remains the same self rank-one projection.

### Canonical nonnegative vacuum

PR #4655 removes the sign ambiguity in the abstract selected top eigenvector. Using the physical rank-one form, unit normalization, and compatibility of real L2 absolute value with scalar multiplication, it proves that the canonical nonnegative physical top eigenvector at (eta=0) is exactly the physical constant-one unit vector.

### Exact probability laws

PR #4656 then works at the correct a.e. representative level and proves:

[
mu_{m vac,0}
=
mu_{m Haar},
]

and

[
mu_{m joint,0}
=
mu_{m Haar}otimesmu_{m Haar}.
]

No arbitrary L2 equivalence-class representative is evaluated pointwise. The final measure equalities are obtained only after proving the relevant Radon--Nikodym densities equal one almost everywhere.

This exact product-law endpoint is the input needed to specialize #4652 to the genuine beta-zero ground-state conditional expectations.

## 5. Immediate next theorem unit

The next mathematical unit should stay on the exact beta-zero ground-state carrier.

The target is:

1. use
   [
   mu_{m joint,0}
   =
   mu_{m Haar}otimesmu_{m Haar}
   ]
   to identify the six right-boundary ground-state conditional expectations with the corresponding product-Haar coordinate/color projections;

2. prove the required pairwise commutation / full-sweep identification on the genuine joint L2 carrier;

3. apply #4652 to obtain the exact beta-zero six-spatial tensorization/frame estimate;

4. identify the common-fixed/centered component relevant to right-boundary physical top-orthogonal lifts;

5. convert the result through #4651 into a strict genuine six-spatial random-scan Rayleigh contraction;

6. feed that contraction into the already-integrated transfer-gap receiver.

This is the clean beta-zero anchor. The later positive-beta theorem must still be volume-uniform; continuity at one fixed finite volume is not enough.

## 6. Positive-temperature / high-temperature continuation after the beta-zero anchor

The repository already has a strong physical high-temperature input: #4648 supplies a positive interval on which the physical influence-envelope sweep is strictly contractive, uniformly in finite volume and background.

What remains is an L2 theorem connecting this physical interdependence control to the genuine ground-state conditional-expectation frame / random-scan Rayleigh estimate.

Two mathematically compatible ingredients are already present:

- exact one-link conditional laws / variance comparison on the ground-state joint law;
- strict volume-independent physical influence contraction.

The required new theorem must preserve the distinction between:

- bounded-test / total-variation-style influence control;
- L2 Rayleigh / Poincare coercivity.

The repository intentionally does not treat the former as a definitional consequence of the latter.

## 7. Downstream obligations

After a scale-independent positive L2 frame/Rayleigh coefficient is established, the existing receivers can produce a uniform finite-volume physical transfer gap.

Still separate after that:

- identify the corresponding Hamiltonian coercive lower bound in the exact physical normalization;
- transport the finite-volume bound through the selected scaling family;
- construct the compatible thermodynamic / infinite-volume physical state;
- complete the continuum OS construction;
- verify the required Euclidean axioms and nontriviality on the same-root physical carrier;
- perform Wightman reconstruction / spectral interpretation;
- establish the continuum Yang--Mills mass gap.

A fixed-volume isolated top eigenvalue is not a volume-uniform gap. A volume-uniform lattice gap is not automatically a continuum Yang--Mills construction.

## Lean / mathlib verification discipline

The repository is pinned to:

- Lean `v4.30.0-rc2`;
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

The lockfiles and repository import graph control compilation, not newer online API signatures.

Recent proof-engineering lessons retained in the canonical workflow:

- use the universe declared by the existing structure; do not replace `Type` with `Type*` without checking;
- `change` only closes definitional equality; theorem-level normalization must happen first;
- check `Finset.sum_mul` / `mul_sum` rewrite orientation explicitly;
- `rw` may close a goal, so a following tactic can legitimately report “no goals to be solved”;
- when an `Lp` coercion or a.e. representative boundary is present, prefer an explicit `calc` chain over forcing a fragile rewrite;
- avoid reverse rewriting with a theorem whose important measure argument is still implicit and unconstrained;
- do not increase heartbeat / recursion depth before checking theorem signatures, rewrite orientation, local instances, or definitional equality;
- broad compact-Dobrushin imports can create duplicate global `SU(N)` measurable-space declarations under the pinned import graph;
- inspect the full changed module, CompileSmoke, and dependency graph, not only the highlighted CI line.

### Latest exact-head validation

For #4656:

- validated head: `fd209bdf7d32b7658d96db018ee7984f6f9621c0`;
- PR Lean Fast Check #14782 / run `35802423074`: completed / success;
- Changed Lean fast check job `106995541127`: success;
- MCP completion receipt `106996352439`: success;
- exact-head `chatgpt-ci-receipt/PR Lean Fast Check`: success.

The theorem-carrier merge commit is
`245d422bef931e769434e2e8607c3d465b9e639b`.

## Navigation

- [ROADMAP.md](ROADMAP.md) — detailed completed and remaining theorem units.
- [MGAP4D/MathlibAnalytic](MGAP4D/MathlibAnalytic) — formal analytic development.
- [Theorem-carrier branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit).

## Status summary

The repository has moved materially beyond response continuity.

The current formal state includes:

- canonical high-temperature response / influence control;
- actual spatial covariance clustering;
- terminal covariance and cubic-shell summability;
- a uniform physical remote residual;
- a positive strict physical full-sweep contraction interval;
- genuine six-spatial L2 Poincare / Rayleigh receivers;
- abstract commuting-projection tensorization;
- exact beta-zero rank-one ambient and physical transfer;
- exact canonical beta-zero vacuum;
- exact beta-zero Haar / pair-Haar ground-state laws.

The immediate theorem frontier is the **beta-zero specialization of commuting-projection tensorization to the genuine ground-state six-spatial conditional expectations**, followed by the volume-uniform positive-beta L2 bridge.
