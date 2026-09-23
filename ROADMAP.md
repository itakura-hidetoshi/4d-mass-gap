# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-23 JST

Repository:

`itakura-hidetoshi/4d-mass-gap`

Unique authoritative theorem-carrier branch:

`formal/real-hilbert-uniform-coercive-strong-limit`

The theorem-bearing baseline immediately before this documentation refresh is:

`245d422bef931e769434e2e8607c3d465b9e639b`

This is the merge commit of PR #4656, **Identify exact beta-zero ground-state laws with Haar product laws**.

The default branch `main` is not theorem authority.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean artifacts;
3. README / ROADMAP;
4. CI receipts;
5. historical summaries or memory.

A docs-only merge may advance a branch pointer without changing the theorem-bearing mathematical baseline.

---

## 0. Claim boundary

The repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

Integrated at the current checkpoint:

- exact finite-volume periodic Wilson / OS / physical-transfer construction;
- canonical vacuum continuation and continuous representatives;
- actual fixed-right response continuity;
- canonical high-temperature half-barrier closure;
- actual physical influence / random-scan contraction;
- spatial covariance clustering;
- terminal covariance decay and cubic-shell summability;
- volume-uniform remote residual;
- positive strict physical full-sweep contraction interval;
- genuine ground-state six-spatial L2 Poincare / Rayleigh receivers;
- abstract commuting-projection tensorization;
- exact beta-zero rank-one ambient and physical transfer;
- exact canonical beta-zero nonnegative vacuum;
- exact beta-zero vacuum measure = Haar;
- exact beta-zero ground-state joint measure = pair Haar.

Not yet integrated:

- a strict volume-uniform genuine ground-state L2 frame / Poincare coefficient for positive beta;
- the resulting scale-independent physical transfer/Hamiltonian gap;
- the full thermodynamic/infinite-volume physical construction;
- the complete continuum OS/Wightman Yang--Mills construction;
- the final continuum mass-gap theorem.

---

## 1. Integrated finite-volume foundation

The older repository already contains the foundational finite-volume Wilson / OS machinery required by the current frontier:

```text
periodic Wilson action / one-slab kernel
  -> product Haar L2
  -> symmetric Hilbert-Schmidt transfer
  -> Gauss-law physical restriction
  -> compact positive physical transfer
  -> top eigenspace / canonical nonnegative vacuum
  -> ground-state transform
  -> vacuum and joint probability laws
  -> genuine one-link conditional expectations
  -> six-spatial / twelve-spatial finite conditional-expectation families
```

This foundation is not being restarted.

---

## 2. Canonical high-temperature response and contraction spine — integrated

### 2.1 Response continuity to half-barrier closure

The current chain begins with the original fixed-right physical response, not a surrogate:

```text
#4634 literal fixed-right target-ratio response continuity
  -> compact-supremum continuity of the canonical response profile
  -> canonical coefficient continuity
  -> half-barrier closure
```

The later high-temperature steps use the existing canonical vacuum and existing probability laws.

### 2.2 Physical influence / random-scan / covariance chain

Integrated chain:

```text
#4637 half-barrier closure
#4638 actual weighted physical influence / response decay
#4639 finite influence-path and resolvent propagation
#4640 canonical random-scan variation contraction
#4641 finite covariance resolvent
#4642 spatial random-scan resolvent
#4643 actual spatial covariance clustering
#4644 concrete two-step terminal covariance decay
#4645 cubic-shell summability -> uniform remote residual
```

For one fixed (s>1), the spatial decay ratio is

[
s^{-1}<1.
]

The resulting bounds are uniform in finite random-scan truncation length and, where stated by the formal theorem, uniform in volume/background.

### 2.3 Oscillation sharpening

The coarse terminal covariance prefactor did not vanish at beta zero. PR #4646 replaces the coarse singleton variation masses by their exact oscillations:

[
e^{2eta}-e^{-2eta},
qquad
e^{16eta}-e^{-16eta}.
]

Hence the sharpened terminal covariance prefactor vanishes exactly at beta zero.

PR #4647 propagates this through the cubic-shell bridge, giving an oscillation-sharpened uniform remote residual

[
ho_{m osc}(s,eta)
]

with

[
ho_{m osc}(s,0)=0.
]

### 2.4 Strict physical sweep gate

The existing envelope coefficient is

[
c_{m env}(eta,ho)
=
18,eta(eta)+ho.
]

PR #4648 proves continuity of

[
etamapsto
c_{m env}(eta,ho_{m osc}(s,eta))
]

at beta zero and proves its value there is zero.

Therefore, for each fixed (s>1), a strictly positive cutoff exists inside the canonical half-barrier interval such that

[
c_{m env}(eta,ho_{m osc}(s,eta))<1.
]

Integrated consequences:

- strict maximum-column contraction for every finite volume/background;
- volume-independent complete-sweep exponential contraction.

### Status of this phase

**Closed.**

No further response/covariance/remote-residual work is needed before beginning the genuine L2 bridge.

---

## 3. Ground-state L2 receiver — integrated

The repository deliberately separates bounded-test / variation contraction from Hilbert-space Rayleigh contraction.

A physical influence column bound is **not** treated as definitionally equivalent to a Poincare theorem.

### 3.1 Dense bounded-core closure — PR #4650

PR #4650 defines the six-spatial normalized residual energy directly on the genuine ground-state joint L2 carrier.

It proves:

- continuity of the six-spatial residual energy;
- bounded strongly measurable concrete representatives form a dense core;
- any relative six-spatial Poincare estimate proved on that dense bounded core extends to the full genuine joint L2 carrier with exactly the same coefficient.

This removes quotient-representative / density closure as a future obstruction.

### 3.2 Genuine six-spatial random-scan receiver — PR #4651

Let (P_c) be the six genuine right-boundary spatial conditional expectations.

Define

[
P_{m rs}
=
rac1{6}sum_{c=1}^{6}P_c.
]

Because each (P_c) is a self-adjoint idempotent,

[
langle P_{m rs}x,xangle
=
rac1{6}sum_c|P_cx|^2.
]

Hence

[
kappa|x|^2
le
rac1{6}sum_c|x-P_cx|^2
]

is equivalent to

[
langle P_{m rs}x,xangle
le
(1-kappa)|x|^2.
]

The physical transfer receiver is already integrated:

if

[
langle P_{m rs}x,xangle
le
q|x|^2
qquad
(0le q<1)
]

on the physical top-orthogonal sector, then

[
rac{3(1-q)}8
le
	ext{physical transfer gap}.
]

There is also a scale-uniform receiver.

### Status of this phase

**Receiver closed; quantitative model-facing premise still open.**

---

## 4. Abstract beta-zero tensorization theorem — integrated

PR #4652 proves the finite real-Hilbert theorem needed for the decoupled endpoint.

For a finite pairwise commuting family of self-adjoint idempotent projections (P_c), let (P_{m sweep}) be an ordered full sweep.

Then

[
|x-P_{m sweep}x|^2
le
sum_c|x-P_cx|^2.
]

Integrated ingredients:

1. self-adjoint idempotents are norm contractions;
2. pairwise commuting projections commute through finite ordered sweeps;
3. coordinate residuals cannot increase under commuting projections;
4. exact one-step Pythagorean decomposition;
5. finite-list sweep tensorization;
6. Fintype full-sweep tensorization.

This theorem is pure Hilbert geometry and introduces no Wilson-specific assumption.

### Status of this phase

**Closed.**

The remaining work is the model specialization.

---

## 5. Exact beta-zero Wilson endpoint — integrated

### 5.1 Ambient Haar-L2 rank-one transfer — PR #4653

At beta zero:

[
K_0(A,B)=1.
]

Let (1_{m Haar}) be the normalized constant-one spatial Haar L2 vector.

The product-Haar kernel vector satisfies

[
K_0
=
1_{m Haar}oxtimes1_{m Haar},
]

and therefore

[
T_0
=
|1_{m Haar}anglelangle1_{m Haar}|.
]

The constant-one mode is fixed.

### 5.2 Physical Gauss-law rank-one transfer — PR #4654

The ambient identity descends to the genuine physical Gauss-law carrier.

At beta zero:

- the canonical physical constant-one vector is a unit vector;
- the physical transfer is its self rank-one projection;
- the physical transfer norm is exactly one;
- the normalized physical transfer is unchanged;
- the physical constant-one vector is fixed.

### 5.3 Canonical nonnegative vacuum — PR #4655

The selected abstract top eigenvector is shown to lie on the constant line.

Unit normalization gives a scalar of absolute value one. Compatibility of real L2 absolute value with scalar multiplication removes the sign ambiguity.

Therefore the canonical nonnegative physical top eigenvector at beta zero is exactly the canonical physical constant-one unit vector.

### 5.4 Exact beta-zero probability laws — PR #4656

The proof stays at the a.e. representative level until final measure equality.

Integrated results:

[
Omega_0=1
quad	ext{Haar-a.e.},
]

[
rac{dmu_{m vac,0}}{dmu_{m Haar}}=1
quad	ext{Haar-a.e.},
]

[
rac{dmu_{m joint,0}}
 {d(mu_{m Haar}otimesmu_{m Haar})}=1
quad	ext{pair-Haar-a.e.}.
]

Hence exactly:

[
oxed{
mu_{m vac,0}
=
mu_{m Haar}
}
]

and

[
oxed{
mu_{m joint,0}
=
mu_{m Haar}otimesmu_{m Haar}.
}
]

### Status of this phase

**Closed.**

---

## 6. Immediate frontier: specialize commuting tensorization to the genuine beta-zero joint law

This is the next exact mathematical obligation.

### 6.1 Identify beta-zero six-spatial conditional expectations with product-Haar projections

Using

[
mu_{m joint,0}
=
mu_{m Haar}otimesmu_{m Haar},
]

prove that the six genuine right-boundary spatial conditional expectations reduce to the expected product-Haar coordinate/color projections.

The theorem should be stated on the existing genuine ground-state joint L2 carrier, not on a substitute finite-state or auxiliary probability space.

### 6.2 Prove pairwise commutation at beta zero

At the product endpoint, the selected beta-zero projections should satisfy the pairwise commutation hypotheses consumed by #4652.

Required output:

[
P_cP_d=P_dP_c
]

for the six genuine beta-zero ground-state spatial projections.

No positive-beta commutativity should be claimed.

### 6.3 Identify the full sweep / common-fixed space

The #4652 tensorization estimate controls

[
|x-P_{m sweep}x|^2.
]

For the physical receiver, identify the sweep/common-fixed component relevant to right-boundary physical lifts.

The desired centered statement should use the already-defined ground-state coarse/retained sector, not introduce a new arbitrary center unless required by the formal API.

### 6.4 Derive the beta-zero six-spatial frame estimate

Combine the exact common-fixed identification with #4652:

[
|x-P_{m sweep}x|^2
le
sum_c|x-P_cx|^2.
]

Convert this to the normalized six-spatial residual.

A strictly positive frame coefficient at beta zero should then follow on the appropriate physical top-orthogonal/right-boundary sector.

The exact coefficient should be claimed only after the Lean theorem determines it.

### 6.5 Feed the result through #4651

Convert the frame estimate into a genuine six-spatial Rayleigh contraction

[
langle P_{m rs}x,xangle
le
q_0|x|^2,
qquad q_0<1.
]

Then apply the existing receiver:

[
rac{3(1-q_0)}8
le
	ext{beta-zero physical transfer gap}.
]

### Acceptance criterion for the next phase

A theorem on the genuine physical top-orthogonal sector with an explicit (q_0<1), or equivalently an explicit (kappa_0>0), obtained without inserting a new unproved Poincare assumption.

---

## 7. Positive-beta / high-temperature L2 bridge

After the exact beta-zero frame is integrated, the main finite-volume quantitative problem is to obtain a **volume-uniform** positive-beta version.

### Available inputs

Already integrated:

1. exact one-link ground-state conditional laws;
2. one-link conditional variance / residual identities;
3. physical influence / response estimates;
4. strict volume-independent complete-sweep variation contraction (#4648);
5. beta-zero exact product law (#4656);
6. dense-core closure (#4650);
7. Rayleigh receiver (#4651).

### Missing theorem

Construct a rigorous bridge of the form

[
	ext{physical interdependence coefficient}<1
quadLongrightarrowquad
	ext{genuine ground-state L2 Rayleigh coefficient}<1,
]

with a constant independent of the finite volume.

This may be formulated as a continuous-state Dobrushin / approximate-tensorization theorem, but the formal statement must match the actual ground-state conditional laws and the repository's target/source orientation.

### Required distinction

Do not identify:

- bounded-test / total-variation influence contraction;

with

- L2 Rayleigh / Poincare contraction.

The latter must be proved.

### Acceptance criterion

Produce (q<1), independent of the finite volume in the selected scaling family, such that

[
langle P_{m rs}x,xangle
le
q|x|^2
]

for every physical top-orthogonal state in the high-temperature regime.

Then #4651 gives the explicit uniform transfer-gap lower bound

[
rac{3(1-q)}8>0.
]

---

## 8. Uniform finite-volume transfer / Hamiltonian gap

Once a scale-independent six-spatial Rayleigh factor (q<1) is available:

1. apply the existing scale-uniform six-spatial transfer-gap receiver;
2. obtain a positive volume-independent physical transfer gap;
3. transport the lower bound to the exact Hamiltonian normalization already used in the physical OS lane;
4. identify the vacuum-orthogonal coercive estimate;
5. preserve the exact same-root physical carrier.

### Acceptance criterion

There exists a scale-independent (gamma>0) such that every member of the selected finite-volume/scaling family has physical excitation gap at least (gamma).

This is still a lattice finite-volume theorem, not yet the continuum mass gap.

---

## 9. Thermodynamic / infinite-volume construction

After the uniform finite-volume gap:

1. choose and formalize the compatible finite-volume embedding / restriction system;
2. prove consistency of the physical vacuum states;
3. establish tightness / compactness or the selected projective/direct-limit replacement;
4. construct the infinite-volume Euclidean physical state;
5. transport reflection positivity, gauge invariance, and the required correlation bounds;
6. retain a nontrivial physical observable algebra.

### Critical requirement

The limiting carrier must be the same-root physical Wilson/OS construction. Auxiliary scalar or unrelated continuum models cannot substitute for this step.

---

## 10. Continuum OS / Wightman construction

Required downstream theorem units include:

- continuum Euclidean invariance in the chosen limiting framework;
- reflection positivity;
- regularity / continuity properties needed by the reconstruction theorem;
- cluster / decay statements strong enough for the physical spectral interpretation;
- nontriviality of the physical Hilbert space and observable content;
- Wightman/OS reconstruction on the same physical theory.

Only after these are established can the continuum Hamiltonian and vacuum sector be interpreted as the target Yang--Mills theory.

---

## 11. Continuum mass gap

The final mass-gap theorem requires a continuum physical Hamiltonian with a unique vacuum line and a positive spectral lower edge on the vacuum-orthogonal sector.

The finite-volume constant must survive every limiting/identification step actually used.

No fixed-volume eigenvalue, auxiliary transfer matrix, or unrelated continuum limit is by itself the Clay mass-gap conclusion.

---

## 12. Lean 4 / mathlib engineering rules

Pinned environment:

- Lean `v4.30.0-rc2`;
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

Operational rules retained from the current proof spine:

1. inspect the whole changed file, CompileSmoke, and import graph when CI fails;
2. do not infer mathematical failure from an elaboration failure;
3. match the existing universe declaration exactly;
4. use theorem rewrites before `change` when equality is not definitional;
5. verify `Finset.sum_mul`, `mul_sum`, and related rewrite direction;
6. remember that `rw` can close a goal;
7. use `ge_of_tendsto'` / `le_of_tendsto'` with the correct inequality orientation;
8. keep local `SU(N)` topology/measurability instances narrowly scoped;
9. avoid broad import diamonds that redeclare pinned global instances;
10. at `Lp` / a.e. boundaries, prefer explicit representative lemmas and `calc` chains;
11. avoid reversing a theorem with unconstrained implicit measure arguments;
12. reduce large operator equalities pointwise before asking the elaborator to normalize them;
13. raise heartbeat / recursion limits only after signature, orientation, local-instance, and definitional-equality checks.

---

## 13. Recent canonical theorem units

| PR | Status | Role |
| --- | --- | --- |
| #4646 | merged | terminal covariance oscillation sharpening |
| #4647 | merged | beta-zero-vanishing remote residual |
| #4648 | merged | strict positive high-temperature physical sweep gate |
| #4650 | merged | six-spatial bounded-core L2 closure |
| #4651 | merged | genuine six-spatial random-scan Rayleigh receiver |
| #4652 | merged | finite tensorization for commuting Hilbert projections |
| #4653 | merged | beta-zero ambient transfer is rank one |
| #4654 | merged | beta-zero physical transfer is rank one |
| #4655 | merged | beta-zero canonical nonnegative vacuum is constant one |
| #4656 | merged | beta-zero vacuum/joint laws are Haar / pair Haar |

Latest theorem-bearing merge before this docs refresh:

`245d422bef931e769434e2e8607c3d465b9e639b`.

Latest validated theorem head:

`fd209bdf7d32b7658d96db018ee7984f6f9621c0`.

PR #4656 validation:

- PR Lean Fast Check #14782;
- run `35802423074`: success;
- changed-Lean job `106995541127`: success;
- MCP completion receipt `106996352439`: success;
- exact-head status receipt: success.

---

## 14. Short restart instruction

At the start of the next theorem thread:

1. fresh re-observe `formal/real-hilbert-uniform-coercive-strong-limit`;
2. do not use `main` as theorem authority;
3. distinguish any docs-only pointer advance from the theorem-bearing baseline;
4. start from the exact beta-zero product-Haar theorem of #4656;
5. specialize #4652 commuting-projection tensorization to the genuine six-spatial beta-zero ground-state conditional-expectation family;
6. feed the resulting strict frame/Rayleigh estimate to #4651;
7. only then begin the volume-uniform positive-beta L2 bridge.
