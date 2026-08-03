# MGAP4D Roadmap

This document records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

It separates:

- theorem infrastructure already replayed on the authoritative carrier;
- concrete finite-volume Wilson results;
- model-specific geometric Osterwalder--Schrader obligations;
- finite-to-continuum analytic obligations; and
- claims that are explicitly not made.

## Snapshot — 2026-08-03 JST

```text
authoritative proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #1365 — Construct shifted geometric Wilson OS kernel operator semigroup

fixed integrated PR head:
  9d275aee4cfaf8c0a056b8e17c466cbc45b9dee5

latest authoritative carrier / squash integration:
  4600dc1488a0b80576d247075ce2afdafd48edfa

latest completed validation:
  PR Lean Fast Check #8625
  run id 30780128446
  job id 91582993004
  completed / success

terminal build:
  Build completed successfully (8758 jobs)

post-merge comparison:
  4600dc1488a0b80576d247075ce2afdafd48edfa
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Open, Draft, stale, superseded, and closed-unmerged pull requests are not part of the authoritative theorem state.

## Proof architecture

The repository now has four converging lanes.

```text
A. continuum reconstruction and spectral infrastructure

Euclidean / OS input
  -> reflection-positive quotient
  -> real Hilbert completion
  -> semigroup and generator
  -> self-adjoint Hamiltonian interfaces
  -> PVM and bounded-Borel calculus
  -> exact lower-spectrum consequences from a supplied spine
  -> concrete continuum Yang--Mills construction [open]


B. finite periodic compact-Haar SU(N) dynamics

Wilson Gibbs measure
  -> exact one-link conditional laws
  -> heat-bath projections and Hamiltonian
  -> explicit Dobrushin influence matrix
  -> genuine centered random-scan Rayleigh certificate
  -> finite Gibbs L2 Poincare/coercivity
  -> centered heat-bath exponential decay
  -> physical scaling family with uniform estimates [open]


C. canonical boundary transfer

boundary Haar L2
  -> canonical boundary-to-Gibbs analysis isometry
  -> adjoint synthesis
  -> compressed Hamiltonian and semigroup
  -> generator leakage / curvature calculus
  -> exact beta-zero closure
  -> nonzero-beta range invariance and OS moment intertwining [open]


D. geometric OS transfer

one-layer Wilson reflection form
  -> OS Hilbert completion
  -> identity-transfer obstruction
  -> independent shifted-kernel certificate
  -> completed positive contraction
  -> discrete natural-time semigroup
  -> exact geometric / unshifted / heat-bath defects
  -> shifted kernel from actual Wilson time geometry [open].
```

The lanes meet only when one concrete approximation family supplies all of the following compatibly:

```text
finite Wilson probability models
geometric time-separated OS kernels
uniform quantitative estimates
a continuum Euclidean measure
operator or closed-form convergence
Hamiltonian identification
spectral transfer
physical-unit normalization.
```

## Status notation

- `[x]` — integrated and replayed on the authoritative carrier.
- `[>]` — immediate active mathematical frontier.
- `[~]` — proposed or Draft work; not an authoritative fact.
- `[ ]` — open.
- `[!]` — explicit claim boundary or anti-goal.

A theorem parametrized by a certificate or construction spine does not construct that certificate or spine. A finite-volume heat-bath gap is not automatically a geometric Euclidean-time gap. A uniform finite-volume theorem is not automatically a continuum theorem. An internal exact normalization is not automatically a physical mass.

---

## Milestone 0 — authoritative carrier and replay discipline

Status: **integrated operational invariant**

- [x] maintain `formal/real-hilbert-uniform-coercive-strong-limit` as the theorem carrier;
- [x] start theorem PRs from the exact current carrier SHA;
- [x] keep ordinary theorem PRs Draft until fixed-head validation is complete;
- [x] use completed workflow, job, step, artifact, and log evidence;
- [x] squash-integrate with the expected head SHA fixed;
- [x] verify post-merge identity with the carrier;
- [x] distinguish integrated facts from stale or superseded branches;
- [!] do not infer theorem status from the default `main` branch alone.

Definition of done:

Every public status statement can be traced to a merged carrier commit and completed validation evidence.

---

## Milestone 1 — OS quotient, real Hilbert completion, semigroup, and Hamiltonian infrastructure

Status: **integrated theorem infrastructure**

- [x] reflection-positive OS seminorm and null-space handling;
- [x] separation quotient and real pre-Hilbert structure;
- [x] complete real Hilbert-space construction;
- [x] represented Euclidean observables and vacuum;
- [x] physical semigroup interfaces;
- [x] strong-continuity routes;
- [x] generator-domain and graph-closure infrastructure;
- [x] self-adjoint Hamiltonian interfaces;
- [x] explicit distinction between supplied analytic data and constructed objects.

Remaining boundary:

- [ ] instantiate the complete route from one nontrivial interacting four-dimensional continuum gauge measure.

---

## Milestone 2 — reconstructed PVM, bounded-Borel calculus, and exact lower spectrum

Status: **integrated from supplied construction data**

- [x] simple-function PVM integration;
- [x] presentation and refinement invariance;
- [x] bounded-Borel operator-norm completion;
- [x] indicator, scalar, subtraction, and multiplicative laws;
- [x] quadratic scalar spectral measures;
- [x] real-Hilbert polarization and symmetry;
- [x] reconstructed scalar and pure-PVM support identification;
- [x] support-based threshold characterization;
- [x] exact-gap theorem package from
  `EuclideanYangMillsContinuumMeasureConstructionSpine`;
- [x] least nonzero spectral value and nonzero-spectrum infimum;
- [x] first-excitation and uniqueness statements.

Claim boundary:

- [!] `exactGapValueReal = 33/20` is an internal normalized theorem route;
- [!] this milestone does not build the physical continuum spine;
- [!] it does not derive `33/20` as a physical Yang--Mills mass.

---

## Milestone 3 — exact finite compact-Haar Wilson conditional dynamics

Status: **integrated**

- [x] finite periodic compact-Haar Wilson Gibbs probability;
- [x] exact one-link conditional probability measures;
- [x] measurable one-link Markov kernels;
- [x] Gibbs reversibility;
- [x] one-link conditional expectation as an `L²` projection;
- [x] heat-bath fluctuation projections and Hamiltonian;
- [x] native Gibbs variance and conditional-pair identities;
- [x] exact Dirichlet-form representation;
- [x] shared-plaquette localization;
- [x] active-neighbor support;
- [x] exact diagonal and inactive-source zero statements;
- [x] symmetric volume-independent Dobrushin matrix.

Explicit coefficient:

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta
```

Proved strict region:

```text
beta < log (19 / 17) / 4.
```

Claim boundary:

- [!] bounded-test / total-variation influence control is not an `L²` Rayleigh theorem.

---

## Milestone 4 — finite Gibbs `L²` Poincare, coercivity, and heat-bath decay

Status: **integrated as a certificate-generated theorem route**

- [x] package scale-wise genuine centered random-scan Rayleigh certificates;
- [x] combine them with explicit Dobrushin matrices;
- [x] replace scale-dependent coefficients by one strict common upper bound;
- [x] derive finite and tail-uniform Gibbs `L²` Poincare inequalities;
- [x] derive vacuum-orthogonal heat-bath coercivity;
- [x] characterize the Gibbs-vacuum kernel;
- [x] construct the full and centered bounded heat-bath exponentials;
- [x] prove the generator orbit equation;
- [x] derive centered exponential norm decay from coercivity;
- [x] propagate decay to finite reflected-integral and vacuum packages.

Integrated quantitative route:

```text
coercivity with gap g
  -> ||exp (-(t/2) H_HB) P_perp f||
       <= sqrt(exp(-g*t)) ||f||.
```

Immediate finite-side obligation:

- [>] generate the centered random-scan Rayleigh theorem directly from the explicit Wilson interaction in the scaling regime of interest, or replace it with a stronger intrinsic `L²` argument;
- [ ] prove a usable common lower bound along an explicitly specified physical lattice trajectory.

---

## Milestone 5 — canonical boundary Haar-to-Gibbs analysis

Status: **integrated**

- [x] construct the reflection-fixed boundary projection;
- [x] prove its product-Haar pushforward law;
- [x] construct boundary-Haar `L²` pullback;
- [x] construct the inverse-square-root Wilson density transport;
- [x] prove exact `L²` inner-product preservation;
- [x] construct the canonical boundary-to-Gibbs linear isometry;
- [x] construct canonical synthesis as its Hilbert adjoint;
- [x] construct the interacting boundary marginal density;
- [x] construct the boundary vacuum moment;
- [x] prove exact vacuum transport;
- [x] prove zero-time analysis/synthesis round trips;
- [x] preserve type separation between boundary Haar and Gibbs carriers.

Definition of done:

The boundary maps are built from actual measure geometry rather than accepted as arbitrary Hilbert-space fields.

---

## Milestone 6 — boundary Hamiltonian, compression, leakage, and semigroup calculus

Status: **integrated**

### Structural compression

- [x] define `H_boundary = A* H_HB A`;
- [x] prove quadratic-form transport, symmetry, and nonnegativity;
- [x] prove boundary-vacuum annihilation;
- [x] construct compressed full and centered heat-bath evolutions;
- [x] prove matrix-coefficient identities;
- [x] prove zero-time identity and centered-sector compatibility.

### Generator leakage

For an isometric analysis `A`, ambient generator `T`, and compression `K = A* T A`, define

```text
D = T A - A K.
```

- [x] prove exact orthogonal decomposition through `D`;
- [x] prove synthesis annihilates the leakage;
- [x] prove the ambient/compressed energy decomposition;
- [x] prove `D = 0` iff exact generator intertwining;
- [x] prove `D = 0` iff analyzed-range invariance;
- [x] prove uniqueness of an exactly intertwined boundary generator.

### Second-moment curvature and semigroup closure

Define

```text
Q = A* T^2 A - K^2.
```

- [x] prove `Q` has nonnegative quadratic form for symmetric `T`;
- [x] prove `<Qx,x> = ||Dx||^2`;
- [x] prove `Q = 0` iff `D = 0`;
- [x] prove zero leakage propagates to every natural power;
- [x] prove zero leakage propagates through the operator exponential;
- [x] prove exact all-time compression, range invariance, and semigroup laws.

General nonzero-coupling frontier:

- [>] prove or quantitatively control the concrete Wilson boundary leakage;
- [>] connect the resulting boundary evolution to geometric OS time.

---

## Milestone 7 — complete beta-zero boundary heat-bath closure

Status: **integrated through PR #1362**

At `beta = 0`:

- [x] prove the Wilson Gibbs density is one;
- [x] prove the boundary marginal is boundary Haar;
- [x] identify canonical analysis with boundary-restriction pullback;
- [x] prove every one-link projection preserves the analyzed range;
- [x] prove every local fluctuation and the full heat-bath Hamiltonian preserve the range;
- [x] prove the concrete generator leakage vanishes;
- [x] prove second-moment curvature vanishes;
- [x] prove sharp boundary Poincare/coercivity constant one;
- [x] exclude nonzero vacuum-orthogonal zero modes;
- [x] construct the exact all-real-time compressed semigroup;
- [x] prove ambient/boundary intertwining;
- [x] prove operator-norm continuity and derivative formulas.

Claim boundary:

- [!] beta-zero heat-bath dynamics is not automatically geometric Euclidean-time translation;
- [!] beta zero is not the interacting continuum Yang--Mills regime.

---

## Milestone 8 — geometric one-layer OS Hilbert completion

Status: **integrated through PR #1364**

- [x] construct an opaque positive-half observable carrier;
- [x] install the actual one-layer Wilson reflection form as a pre-inner-product core;
- [x] identify OS nullity with zero Wilson quadratic form;
- [x] form the separation quotient;
- [x] complete the geometric OS Hilbert space;
- [x] construct a dense raw-observable embedding;
- [x] prove its inner product is exactly the Wilson one-layer form;
- [x] construct the canonical identity transfer;
- [x] prove exact reproduction of all unshifted matrix elements;
- [x] prove global uniqueness from dense matrix elements;
- [x] prove every nonidentity candidate has a nonzero matrix-element witness.

Central obstruction:

```text
all unshifted Wilson one-layer matrix elements are reproduced
  iff
the bounded transfer operator is identity.
```

Therefore:

- [!] a nontrivial geometric transfer requires shifted-kernel information not contained in the unshifted reflection form.

---

## Milestone 9 — independent shifted geometric OS operator and discrete semigroup

Status: **integrated through PR #1365**

From an independent shifted-kernel certificate:

- [x] require exact raw-carrier matrix-element realization;
- [x] require contraction;
- [x] require OS symmetry and nonnegative quadratic form;
- [x] derive OS-null preservation;
- [x] descend the shift to the separation quotient;
- [x] extend uniquely to the completed OS Hilbert space;
- [x] prove the completed operator is symmetric, positive, and contractive;
- [x] define natural-number iterates;
- [x] prove the additive discrete semigroup law;
- [x] prove exact represented-state action;
- [x] prove exact iterated shifted-kernel matrix elements.

Claim boundary:

- [!] the shifted-kernel certificate remains independent input;
- [!] no continuous-time logarithm or unbounded generator is constructed here;
- [!] no continuum limit follows from the discrete semigroup alone.

---

## Milestone 10 — exact comparison defects among the three dynamics

Status: **integrated**

The repository keeps distinct:

```text
geometric Wilson shifted time
random-scan path-space Markov time
canonical beta-zero boundary heat-bath time.
```

- [x] define the geometric matrix-element defect;
- [x] prove zero matrix defect iff exact realization;
- [x] define same-carrier natural-power defects;
- [x] prove all-time equality iff one-step equality;
- [x] define cross-carrier isometric intertwining defects;
- [x] prove zero defect propagates to every natural power;
- [x] prove zero defect gives exact adjoint-compression equality;
- [x] prove nonzero defect supplies an exact no-go witness;
- [x] classify simultaneous realization of the unshifted form and beta-zero heat-bath step;
- [x] prove simultaneous realization forces identity transfer and identity heat-bath step.

Anti-identification theorem:

A common exponential or semigroup shape does not identify the underlying dynamics. Equality must be proved through the explicit zero-defect theorem.

---

## Milestone 11 — construct the actual nonzero-coupling geometric Wilson shift

Status: **immediate active frontier**

- [>] define a time-separated finite-volume Wilson kernel from actual gauge configurations and reflection geometry;
- [>] prove measurability and integrability of the shifted kernel;
- [>] prove exact realization by a raw positive-half shift;
- [>] prove contraction on the one-layer OS seminorm;
- [>] prove OS symmetry and positivity;
- [>] prove OS-null preservation;
- [>] instantiate the integrated shifted-kernel certificate;
- [>] compute the unshifted matrix defect;
- [>] compute the boundary heat-bath bridge defect;
- [>] identify a regime in which the relevant defect vanishes or is quantitatively controlled.

Definition of done:

The shifted operator is generated from actual Wilson time geometry rather than supplied as abstract certificate data.

Failure is also mathematically informative: an explicit nonzero defect or failed positivity condition should be recorded as a no-go theorem rather than hidden by changing the meaning of time.

---

## Milestone 12 — exact OS boundary-moment intertwining

Status: **open**

For the canonical boundary analysis `A`, adjoint synthesis `A*`, and a genuine geometric OS transfer `T_OS`, prove an exact relation of the form

```text
A* (finite Gibbs evolution) A
  = geometric OS transfer
```

on a dense boundary-observable core, or prove the corresponding matrix elements agree.

Tasks:

- [ ] identify the correct time normalization and half-time convention;
- [ ] prove boundary observables represent the intended time-zero OS states;
- [ ] prove the shifted Wilson kernel gives the required boundary moments;
- [ ] prove equality with the compressed finite Gibbs evolution, or quantify the defect;
- [ ] extend from the dense observable image to the completed carrier;
- [ ] preserve vacuum centering and the exact decay rate.

Claim boundary:

- [!] random-scan or heat-bath time must not be renamed as Euclidean time;
- [!] the theorem must arise from the model's reflection/translation geometry.

---

## Milestone 13 — tail-uniform finite-volume control in a physical scaling regime

Status: **open**

Specify one concrete approximation trajectory:

```text
lattice spacing a_n -> 0
physical volume or torus size L_n
coupling beta_n
gauge group SU(N)
boundary and time-step conventions.
```

Then prove:

- [ ] nondegenerate periodic geometry on the tail;
- [ ] a genuine scale-wise `L²` Rayleigh theorem;
- [ ] one positive common gap or a controlled renormalized gap;
- [ ] compatibility of the Dobrushin/spectral region with the chosen `beta_n`;
- [ ] uniform boundary-transfer estimates;
- [ ] uniform geometric shifted-kernel estimates;
- [ ] tightness or compactness estimates for the Euclidean measures;
- [ ] uniform regularity and reflection-positive correlation bounds.

The current strict Dobrushin region is a valid finite small-coupling theorem. It is not automatically compatible with the asymptotically free four-dimensional continuum trajectory.

---

## Milestone 14 — continuum Euclidean Yang--Mills construction

Status: **open**

- [ ] construct a projectively or weakly convergent family of finite gauge measures;
- [ ] identify a nontrivial continuum Euclidean field law;
- [ ] prove Euclidean covariance in the required form;
- [ ] prove reflection positivity of the limiting Schwinger functions;
- [ ] prove regularity and clustering;
- [ ] construct gauge-invariant continuum observables;
- [ ] prove nontriviality and interaction;
- [ ] instantiate the existing OS reconstruction interfaces.

Definition of done:

A concrete continuum probability/Schwinger system supplies the currently abstract construction spine.

---

## Milestone 15 — operator/form convergence and Hamiltonian identification

Status: **open**

- [ ] place finite and continuum carriers on compatible comparison maps;
- [ ] prove strong resolvent, graph, Mosco, or another adequate closed-form convergence theorem;
- [ ] transfer finite coercivity without losing the vacuum sector;
- [ ] identify the limiting semigroup with reconstructed Euclidean time translation;
- [ ] identify its self-adjoint generator as the physical Hamiltonian;
- [ ] prove the normalized vacuum is the complete zero-energy kernel;
- [ ] exclude spectral pollution below the proposed threshold.

No uncompressed operator-norm convergence is required unless a theorem specifically needs it. The convergence topology must be strong enough for the claimed spectral conclusion and no stronger than justified by the model.

---

## Milestone 16 — spectral transfer and physical mass normalization

Status: **open**

- [ ] transfer a positive lower spectral bound to the continuum Hamiltonian;
- [ ] prove the nonzero spectrum is nonempty;
- [ ] identify whether the threshold is continuous support or an eigenvalue;
- [ ] prove positive spectral weight for a concrete gauge-invariant observable if required;
- [ ] relate lattice time units to physical units;
- [ ] determine the renormalized physical mass scale;
- [ ] distinguish a lower bound, an attained threshold, and an exact eigenvalue;
- [ ] compare the result with `exactGapValueReal` only after normalization is proved.

Claim boundary:

- [!] the internal value `33/20` is not a physical prediction without this milestone.

---

## Milestone 17 — final theorem and independent review

Status: **open**

A final existence-and-mass-gap theorem would require a single dependency chain proving:

```text
nontrivial four-dimensional continuum Yang--Mills existence
OS/Wightman reconstruction
physical Hilbert space and Hamiltonian
unique vacuum sector
strict positive mass gap
all model-specific finite-to-continuum hypotheses
physical normalization.
```

Final review requirements:

- [ ] complete theorem dependency index;
- [ ] replay from a fresh pinned environment;
- [ ] no hidden supplied field equivalent to the target theorem;
- [ ] no conflation of finite heat-bath and geometric Euclidean time;
- [ ] no inference of `L²` coercivity from total variation alone;
- [ ] no stale-branch theorem counted as integrated;
- [ ] independent mathematical review of the model construction and analytic transfer;
- [ ] independent Lean review of the principal theorem chain.

Until then:

```text
unconditional Clay Millennium theorem: not claimed
independent external mathematical consensus: not claimed.
```

---

## Immediate next theorem units

The preferred mathematical order is:

```text
1. define the concrete finite Wilson shifted geometric kernel;
2. prove or refute its OS positivity, contraction, and null preservation;
3. instantiate the completed shifted OS operator;
4. evaluate the geometric/unshifted matrix defect;
5. evaluate the geometric/beta-zero heat-bath bridge defect;
6. extend the comparison to nonzero coupling;
7. prove the actual boundary-moment intertwining or a quantitative substitute;
8. generate the scale-wise L2 Rayleigh theorem from the explicit interaction;
9. specify a physical continuum scaling trajectory;
10. prove tail-uniform finite and geometric transfer estimates;
11. construct the continuum Euclidean measure;
12. prove operator/form convergence and spectral transfer.
```

Each integration unit should close a mathematically coherent package. Small wrappers, aliases, receipts, or smoke files count as progress only when they eliminate an actual supplied assumption, expose a necessary invariant, or connect two previously distinct theorem carriers.

## Permanent anti-goals

- [!] do not weaken theorem statements, physical assumptions, mass values, or decay rates to obtain compilation;
- [!] do not identify random-scan Markov time with geometric Euclidean time by notation;
- [!] do not infer `L²` Poincare from total-variation Dobrushin control alone;
- [!] do not treat a supplied construction spine as a constructed continuum model;
- [!] do not treat the beta-zero product theory as the interacting continuum theory;
- [!] do not treat `exactGapValueReal = 33/20` as a physical mass before normalization;
- [!] do not use open, Draft, stale, or superseded branches as authoritative theorem evidence;
- [!] do not replace a concrete model theorem by an opaque certificate whose fields restate the desired conclusion.

## Final definition of done

The project reaches its mathematical objective only when the authoritative carrier contains a replayable, concrete, non-circular chain

```text
finite Wilson gauge models
  -> geometric OS time transfer
  -> uniform quantitative finite estimates
  -> nontrivial continuum Euclidean Yang--Mills measure
  -> reconstructed physical Hamiltonian
  -> strict positive spectral gap
```

with every model-specific assumption discharged by definitions and theorems for one explicit approximation family.
