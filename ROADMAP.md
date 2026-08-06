# MGAP4D Roadmap

This document records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

It separates:

- theorem infrastructure replayed on the authoritative carrier;
- concrete compact-gauge and finite `Z₂` Wilson results;
- actual geometric one-slab transfer results;
- high-temperature posterior and coupling results;
- finite-to-continuum analytic obligations; and
- claims that are explicitly not made.

## Snapshot — 2026-08-06 JST

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #1391
  Construct correct-marginal parallel Doob coupling
  and spatial sandwich contraction

fixed integrated PR head:
  a276308b86d060f6f406de0f45e2afe51fb68192

latest authoritative carrier / squash integration:
  eaade95477ee0cf354d265b14d08123aec1ff52f

latest completed validation:
  PR Lean Fast Check #9184
  run id 31078935258
  job id 92543058944
  completed / success

terminal build:
  Build completed successfully (8686 jobs)

post-merge comparison:
  eaade95477ee0cf354d265b14d08123aec1ff52f
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

Open, Draft, stale, superseded, and closed-unmerged pull requests are not part of the authoritative theorem state.

## Proof architecture

The repository now has five connected lanes.

```text
A. continuum reconstruction and exact-spectrum infrastructure

Euclidean / OS input
  -> reflection-positive quotient
  -> real Hilbert completion
  -> semigroup and generator
  -> self-adjoint Hamiltonian interfaces
  -> PVM and bounded-Borel calculus
  -> exact lower-spectrum consequences from a supplied spine
  -> concrete interacting continuum construction [open]


B. finite periodic compact-Haar SU(N) analysis

Wilson Gibbs law
  -> exact conditional laws
  -> heat-bath projections and Hamiltonian
  -> explicit Dobrushin matrices
  -> genuine L2 Rayleigh data
  -> finite Gibbs Poincare/coercivity
  -> centered decay and conditional continuum transfer


C. canonical boundary analysis and comparison

boundary Haar L2
  -> canonical Haar-to-Gibbs isometry
  -> Hilbert-adjoint synthesis
  -> compressed Hamiltonian and semigroups
  -> leakage and curvature defects
  -> exact beta-zero closure
  -> explicit cross-dynamics comparison defects


D. actual finite even-four-torus Z2 geometric transfer

finite-period configuration-shift no-go
  -> adjacent-slice one-slab Wilson kernel
  -> residual Gauss projection and temporal-link sum
  -> symmetric positive normalized transfer
  -> full finite spectral decomposition
  -> Perron ground simplicity and injectivity
  -> positive gap at every finite volume
  -> crossing-only volume-independent gap


E. actual high-temperature Perron posterior

Perron-ground and posterior continuity at beta = 0
  -> canonical envelope and bidirectional bootstrap
  -> positive volume-independent coupling cutoff
  -> actual strict posterior Dobrushin data
  -> correct-marginal parallel overlap coupling
  -> Hamming contraction and spatial-sandwich stability
  -> random-scan uniqueness, mixing, TV and strong convergence
```

The lanes meet only when one concrete approximation family supplies compatible geometric transfer, uniform quantitative estimates, continuum probability data, convergence, Hamiltonian identification, and physical normalization.

## Status notation

- `[x]` — integrated and replayed on the authoritative carrier.
- `[>]` — immediate active mathematical frontier.
- `[~]` — proposed or Draft work; not an authoritative fact.
- `[ ]` — open.
- `[!]` — explicit claim boundary or anti-goal.

A theorem parametrized by a certificate or construction spine does not construct that certificate or spine. A finite Markov-chain contraction is not automatically a geometric Euclidean-time spectral gap. A positive gap at every finite volume is not automatically a uniform gap. An internal exact normalization is not automatically a physical mass.

---

## Milestone 0 — authority, replay, and public synchronization

Status: **integrated operational invariant**

- [x] maintain `formal/real-hilbert-uniform-coercive-strong-limit` as the theorem carrier;
- [x] start theorem PRs from the exact current carrier SHA;
- [x] keep ordinary theorem PRs Draft until fixed-head validation is complete;
- [x] use completed workflow, job, step, artifact, and log evidence;
- [x] squash-integrate with `expected_head_sha` fixed;
- [x] verify post-merge identity with the carrier;
- [x] distinguish integrated facts from stale or superseded branches;
- [x] use `main` as the public landing surface;
- [x] synchronize README and ROADMAP from the validated carrier to `main` after integration;
- [!] do not infer mathematical authority from stale `main` content or from open PRs.

Definition of done:

Every public status statement is traceable to one merged carrier commit and completed validation evidence, and the public landing page is synchronized after the authoritative documentation merge.

---

## Milestone 1 — OS quotient, Hilbert completion, semigroup, and Hamiltonian infrastructure

Status: **integrated theorem infrastructure**

- [x] reflection-positive OS seminorm and null-space handling;
- [x] separation quotient and real pre-Hilbert structure;
- [x] complete real Hilbert-space construction;
- [x] represented Euclidean observables and vacuum;
- [x] physical semigroup interfaces;
- [x] strong-continuity routes;
- [x] generator-domain and graph-closure infrastructure;
- [x] self-adjoint Hamiltonian interfaces;
- [x] explicit separation between supplied analytic data and constructed objects.

Remaining boundary:

- [ ] instantiate the route from one nontrivial interacting four-dimensional continuum gauge measure.

---

## Milestone 2 — PVM, bounded-Borel calculus, and exact lower spectrum

Status: **integrated from supplied construction data**

- [x] simple-function PVM integration;
- [x] refinement and presentation invariance;
- [x] bounded-Borel operator-norm completion;
- [x] indicator, scalar, subtraction, and multiplicative laws;
- [x] quadratic scalar spectral measures;
- [x] real-Hilbert polarization and symmetry;
- [x] scalar and pure-PVM support identification;
- [x] support-based threshold characterization;
- [x] exact-gap theorem package from `EuclideanYangMillsContinuumMeasureConstructionSpine`;
- [x] least nonzero spectral value and nonzero-spectrum infimum;
- [x] first-excitation and uniqueness statements.

Claim boundary:

- [!] `exactGapValueReal = 33/20` is an internal normalized theorem route;
- [!] this milestone does not construct the physical continuum spine;
- [!] it does not derive `33/20` as a physical Yang--Mills mass.

---

## Milestone 3 — finite compact-Haar `SU(N)` Gibbs and heat-bath analysis

Status: **integrated**

- [x] finite periodic compact-Haar Wilson Gibbs probability;
- [x] exact one-link conditional probability laws;
- [x] measurable one-link Markov kernels;
- [x] Gibbs reversibility and Hilbert projection structure;
- [x] heat-bath Hamiltonian and native Dirichlet form;
- [x] conditional variance and independent-pair identities;
- [x] shared-plaquette localization and active-neighbor support;
- [x] explicit volume-independent bounded-test Dobrushin matrices;
- [x] finite Gibbs `L²` Poincare/coercivity from coefficient bounds plus genuine centered Rayleigh data;
- [x] centered heat-bath exponential decay;
- [x] finite reflected-integral and conditional continuum coercivity routes.

Explicit coefficient:

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta
```

Proved strict bounded-test region:

```text
beta < log (19 / 17) / 4.
```

Claim boundary:

- [!] total-variation influence control alone is not an `L²` Rayleigh theorem;
- [!] this finite compact-Haar lane is not yet an actual adjacent-slice compact-gauge transfer construction.

---

## Milestone 4 — canonical boundary analysis, compression, and beta-zero closure

Status: **integrated**

- [x] reflection-fixed boundary projection and product-Haar pushforward;
- [x] boundary-Haar `L²` pullback;
- [x] inverse-square-root Gibbs-density transport;
- [x] canonical boundary-to-Gibbs linear isometry;
- [x] canonical synthesis as the real-Hilbert adjoint;
- [x] boundary marginal vacuum normalization and exact vacuum transport;
- [x] compressed boundary Hamiltonian `A* H_HB A`;
- [x] full and centered compressed heat-bath evolutions;
- [x] generator leakage decomposition;
- [x] second-moment curvature `Q` with `<Qx,x> = ||Dx||²`;
- [x] zero-defect all-time semigroup and exact intertwining;
- [x] complete beta-zero normalization, range invariance, sharp coercivity one, and zero-mode exclusion.

Claim boundary:

- [!] heat-bath time is not automatically geometric Euclidean time;
- [!] beta zero is not an interacting continuum regime;
- [ ] nonzero-coupling compact-gauge analyzed-range invariance and geometric moment identification remain open.

---

## Milestone 5 — geometric one-layer completion and no-go theorems

Status: **integrated**

- [x] complete the unshifted Wilson one-layer reflection form to a geometric OS Hilbert space;
- [x] prove every bounded operator reproducing all unshifted matrix elements is the identity;
- [x] construct shifted-kernel quotient/completion/semigroup machinery from explicit certificate data;
- [x] define exact defects against unshifted and heat-bath dynamics;
- [x] construct the actual periodic even-four-torus one-step time translation;
- [x] prove its finite period;
- [x] prove finite-order + contraction + symmetry + positivity forces identity;
- [x] conclude that a nontrivial geometric transfer cannot be an invertible periodic configuration permutation.

Required replacement:

```text
periodic configuration permutation
  -> invalid for nontrivial positive OS time

adjacent-slice slab kernel after interior summation
  -> required construction.
```

---

## Milestone 6 — actual finite `Z₂` adjacent-slice one-slab transfer

Status: **integrated**

- [x] define the actual spatial time-slice boundary carrier;
- [x] define temporal-gauge crossing plaquette factors;
- [x] prove the crossing kernel is a finite nonnegative Gram kernel;
- [x] insert actual spatial half-actions;
- [x] prove the full slab kernel equals the Wilson Boltzmann weight;
- [x] construct the finite Euclidean boundary Hilbert operator;
- [x] prove symmetry and nonnegative quadratic form;
- [x] normalize by operator norm and prove norm one and contractivity;
- [x] construct natural-time powers and additive semigroup law;
- [x] prove nonidentity by explicit off-diagonal matrix elements;
- [x] construct the residual slice-gauge action and Gauss projector;
- [x] compress to the gauge-invariant boundary Hilbert carrier;
- [x] restore temporal-link fields and perform the exact finite temporal-link sum;
- [x] construct the unfixed-gauge transfer with separate boundary gauge invariance.

Definition of done:

The finite `Z₂` geometric-time carrier is generated from an actual adjacent-slice Wilson action, not from a Markov-chain relabeling or a periodic configuration permutation.

---

## Milestone 7 — finite spectral decomposition and Perron ground

Status: **integrated**

- [x] construct a canonical finite-dimensional real eigenbasis;
- [x] prove transfer eigenvalues lie in `[0,1]`;
- [x] construct the positive spectral-support Hilbert space;
- [x] define support energy `-log(lambda)` only for `lambda > 0`;
- [x] prove exact transfer/Hamiltonian natural-time relations;
- [x] stratify ground, strictly excited, and null sectors;
- [x] construct exact synthesis and coordinate restrictions;
- [x] characterize kernel, fixed space, and range;
- [x] assign separate infinite extended energy to null modes;
- [x] prove existence of a norm-one ground mode;
- [x] prove Perron ground-state simplicity from strict entrywise positivity;
- [x] obtain a unique pointwise-positive ground ray at every finite volume.

Claim boundary:

- [!] ground-state simplicity does not by itself prove a uniform excitation gap.

---

## Milestone 8 — strict-coupling gaps at every finite `Z₂` volume

Status: **integrated**

Under

```text
0 < beta
energyIdentity < energyNontrivial,
```

the repository proves:

- [x] strict ordering of the two local Wilson weights;
- [x] positive definiteness of the local two-state crossing matrix;
- [x] preservation of positive definiteness under finite tensor products;
- [x] positive definiteness of the temporal crossing kernel at every finite side;
- [x] preservation under positive spatial diagonal congruence;
- [x] injectivity of raw, normalized, and Gauss-compressed transfers;
- [x] absence of the null sector at every finite volume;
- [x] a geometric gauge-orbit nonidentity witness at every finite volume;
- [x] nonempty strictly excited spectrum at every finite volume;
- [x] a strictly positive exact excitation gap at every finite volume;
- [x] exact excited-coordinate exponential decay.

Claim boundary:

- [!] the finite-volume gap may depend on the side parameter;
- [!] `forall H, 0 < Delta_H` does not imply `exists Delta_* > 0, forall H, Delta_* <= Delta_H`.

---

## Milestone 9 — uniform-gap equivalences and crossing-only closure

Status: **integrated**

### Generic equivalences

- [x] common excited eigenvalue cap below one;
- [x] uniform centered Rayleigh contraction;
- [x] uniform centered Poincare coercivity;
- [x] positive volume-independent energy floor;
- [x] exact conversion among all four formulations.

### Actual crossing-only theorem

For the normalized temporal-crossing tensor product:

- [x] identify the local sign eigenvalue `q`;
- [x] prove a dimension-independent centered Rayleigh bound;
- [x] prove Poincare coercivity `kappa = 1 - q`;
- [x] transport the theorem to arbitrary finite `Z₂` link configurations;
- [x] identify the normalized raw crossing transfer with the tensor kernel;
- [x] preserve the estimate under Gauss compression;
- [x] prove volume-independent natural-time decay with `Delta_cross = -log(q)`.

Claim boundary:

- [!] this is the crossing-only backbone;
- [!] the full transfer includes the spatial half-action sandwich.

---

## Milestone 10 — exact spatial-sandwich factorization and local-stability boundary

Status: **integrated structural layer**

- [x] prove finite kernel sandwich factorization `Op(aKa) = M_a * Op(K) * M_a`;
- [x] prove the actual full one-slab factorization through the crossing kernel;
- [x] compute exact global spatial-weight oscillation;
- [x] prove crude whole-volume extremal comparison is volume dependent;
- [x] define a local uniform degradation certificate `epsilon < kappa_cross`;
- [x] prove such a certificate implies a full-transfer uniform Rayleigh/Poincare/gap package.

The original missing input was a volume-independent local control of the spatial sandwich. Milestones 11 and 12 construct the current actual high-temperature posterior mechanism intended to supply that local control.

---

## Milestone 11 — actual high-temperature Perron posterior closure

Status: **integrated**

- [x] construct canonical non-strict conditional `L¹` influence matrices;
- [x] develop reciprocal row/column response without assuming strictness;
- [x] construct exact local shared-plaquette influence rows;
- [x] prove all-volume finite incidence bounds;
- [x] construct canonical envelope kernels and finite bootstrap stages;
- [x] prove bidirectional row/column coefficient recurrences;
- [x] prove persistent barrier propagation after strict entry;
- [x] remove finite-depth terminal residual through asymptotic response;
- [x] construct a continuous first-exit barrier theorem;
- [x] prove continuity of finite inverses and Perron eigenvalues;
- [x] construct a canonically normalized positive Perron ground of total mass one;
- [x] prove actual unfixed-gauge Perron-ground continuity;
- [x] prove continuity of actual conditional laws and influence entries;
- [x] prove exact zero-coupling posterior and zero influence seed;
- [x] select a positive volume-independent coupling cutoff;
- [x] instantiate actual strict row-and-column Dobrushin data at every finite volume and environment for `0 < beta <= cutoff`.

Fixed continuation barrier:

```text
rho = 1/2.
```

Claim boundary:

- [!] the cutoff is an existence result from exact zero-coupling continuity;
- [!] this is a finite high-temperature `Z₂` theorem, not an asymptotically free continuum trajectory.

---

## Milestone 12 — correct-marginal parallel coupling and spatial stability

Status: **integrated through PR #1391**

- [x] construct exact finite overlap couplings with prescribed marginals;
- [x] construct coordinatewise product couplings for parallel conditional resampling;
- [x] prove exact left and right parallel-kernel marginal laws;
- [x] derive coordinate disagreement and expected Hamming bounds;
- [x] construct bidirectional strict Dobrushin coupling data;
- [x] specialize to the actual finite even-four-torus Perron posterior throughout the high-temperature interval;
- [x] prove arbitrary-slice expected Hamming contraction with factor `1/2 * rho < 1`;
- [x] prove spatial-sandwich stability under common exterior data;
- [x] iterate the random-scan overlap coupling;
- [x] prove stationary uniqueness and mixing;
- [x] derive total-variation control and strong convergence;
- [x] derive Hamming-Lipschitz observable response;
- [x] transport coupling through residual-gauge and unfixed-gauge mixtures.

Actual stability form:

```text
expected disagreement
  <= (1/2 * rho) * Hamming distance,

common exterior outside interior
  -> expected disagreement
       <= (1/2 * rho) * interior.card.
```

Claim boundary:

- [!] these coupling and mixing results concern the posterior parallel/random-scan dynamics;
- [!] their contraction factor is not definitionally the spectral cap of the geometric full one-slab transfer.

---

## Milestone 13 — full geometric one-slab uniform-gap bridge

Status: **immediate active frontier**

Use the integrated data

```text
crossing-only geometric gap
actual Perron ground and Doob posterior
strict bidirectional posterior Dobrushin data
correct-marginal parallel coupling
spatial-sandwich Hamming stability
observable-response transport
```

to prove a theorem on the **actual full spatially sandwiched one-slab transfer**.

Required tasks:

- [>] identify the exact posterior/Doob representation of the normalized full transfer on the ground-centered sector;
- [>] convert correct-marginal coupling stability into a quadratic-form or operator contraction estimate for the geometric transfer;
- [>] prove a volume-independent centered Rayleigh cap strictly below one;
- [>] equivalently prove one volume-independent full-transfer Poincare coercivity constant;
- [>] equivalently construct one positive lower bound for every full-transfer finite-volume excitation gap;
- [>] retain exact dependence on the high-temperature cutoff and barrier;
- [>] keep random-scan/heat-bath time separate from geometric one-slab time;
- [>] propagate the resulting gap to natural-time geometric decay;
- [>] record an explicit obstruction if the coupling estimate is insufficient for the required Hilbert-space bound.

Definition of done:

```text
exists Delta_full > 0,
  forall finite side H,
    Delta_full <= fullGeometricExcitationGap(H)
```

under one explicit, volume-independent finite `Z₂` high-temperature regime, proved from the actual full transfer rather than from a differently timed Markov chain.

---

## Milestone 14 — compact `SU(2)` / `SU(N)` geometric one-slab extension

Status: **open**

- [ ] replace finite `Z₂` temporal-link sums by normalized compact Haar integration;
- [ ] construct the actual compact-gauge adjacent-slice kernel;
- [ ] prove gauge equivariance and Gauss projection;
- [ ] prove symmetry, positivity, nontriviality, and normalization;
- [ ] construct or characterize the compact Perron ground;
- [ ] construct compact conditional/posterior influence data;
- [ ] prove a correct-marginal compact coupling or another valid local stability theorem;
- [ ] derive a geometric full-transfer spectral cap or coercivity bound;
- [ ] preserve the distinction from the existing compact heat-bath lane.

The finite compact-Haar Gibbs/heat-bath infrastructure is already integrated. What remains is the **geometric adjacent-slice transfer** and its quantitative compact-gauge spectral analysis.

---

## Milestone 15 — physical scaling and tail-uniform estimates

Status: **open**

Specify one concrete approximation trajectory:

```text
lattice spacing a_n -> 0
physical volume or torus size L_n
coupling beta_n
gauge group SU(N)
time-step and boundary conventions.
```

Then prove:

- [ ] compatibility of the finite high-temperature or alternative analytic regime with the chosen `beta_n`;
- [ ] one controlled geometric transfer gap in physical units;
- [ ] uniform reflection-positive correlation estimates;
- [ ] tightness or compactness of Euclidean measures;
- [ ] uniform regularity and clustering;
- [ ] stable boundary/OS comparison maps;
- [ ] a nontrivial interacting limit rather than a beta-zero or decoupled limit.

Claim boundary:

- [!] a finite high-temperature cutoff is not automatically compatible with four-dimensional asymptotic freedom or a physical continuum trajectory.

---

## Milestone 16 — continuum Euclidean Yang--Mills construction

Status: **open**

- [ ] construct a projectively or weakly convergent finite gauge family;
- [ ] identify a nontrivial continuum Euclidean field law;
- [ ] prove Euclidean covariance;
- [ ] prove reflection positivity of the limiting Schwinger functions;
- [ ] prove regularity and clustering;
- [ ] construct gauge-invariant continuum observables;
- [ ] prove nontriviality and interaction;
- [ ] instantiate the existing OS reconstruction interfaces and the currently supplied continuum spine.

Definition of done:

A concrete continuum probability/Schwinger system supplies the model fields currently accepted as construction-spine data.

---

## Milestone 17 — operator/form convergence and Hamiltonian identification

Status: **open**

- [ ] place finite and continuum carriers on compatible comparison maps;
- [ ] prove strong resolvent, graph, Mosco, or another adequate closed-form convergence theorem;
- [ ] transfer finite geometric coercivity without losing the vacuum sector;
- [ ] identify the limiting semigroup with reconstructed Euclidean time translation;
- [ ] identify its self-adjoint generator as the physical Hamiltonian;
- [ ] prove the normalized vacuum is the complete zero-energy kernel;
- [ ] exclude spectral pollution below the proposed threshold.

The topology must be strong enough for the spectral conclusion and no stronger than justified by the model.

---

## Milestone 18 — spectral transfer and physical normalization

Status: **open**

- [ ] transfer a positive lower spectral bound to the continuum Hamiltonian;
- [ ] prove the nonzero continuum spectrum is nonempty;
- [ ] determine whether the threshold is continuous support or an eigenvalue;
- [ ] prove positive spectral weight for a concrete gauge-invariant observable if required;
- [ ] relate lattice natural time to physical time;
- [ ] determine the renormalized physical mass scale;
- [ ] distinguish lower bound, attained threshold, and exact eigenvalue;
- [ ] compare with `exactGapValueReal` only after normalization is proved.

Claim boundary:

- [!] internal `33/20` is not a physical prediction before this milestone.

---

## Milestone 19 — final theorem and independent review

Status: **open**

A final existence-and-mass-gap theorem requires one non-circular dependency chain proving:

```text
nontrivial four-dimensional continuum Yang--Mills existence
OS/Wightman reconstruction
physical Hilbert space and Hamiltonian
unique vacuum sector
strict positive physical mass gap
all finite-to-continuum hypotheses
physical normalization.
```

Final review requirements:

- [ ] complete theorem dependency index;
- [ ] replay from a fresh pinned environment;
- [ ] no hidden supplied field equivalent to the target theorem;
- [ ] no conflation of random-scan, heat-bath, and geometric time;
- [ ] no inference of `L²` coercivity from total variation alone;
- [ ] no inference of uniformity from pointwise finite-volume positivity;
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
1. expose the exact ground-state Doob representation of the full one-slab transfer;
2. connect the actual parallel posterior coupling to centered transfer matrix elements;
3. prove a full-transfer centered Rayleigh contraction below one;
4. convert it to Poincare coercivity and a uniform finite Z2 geometric gap;
5. prove natural-time full-transfer exponential decay;
6. isolate which estimates survive compact Haar replacement;
7. construct the compact SU(2)/SU(N) adjacent-slice transfer;
8. prove compact local stability and a geometric spectral cap;
9. specify a physical continuum scaling trajectory;
10. prove tail-uniform measure and transfer estimates;
11. construct the continuum Euclidean measure;
12. prove operator/form convergence and spectral transfer.
```

Each integration unit should close a mathematically coherent package. Small aliases, wrappers, receipts, or smoke files count as progress only when they eliminate a real supplied assumption, expose a necessary obstruction, or connect previously distinct theorem carriers.

## Permanent anti-goals

- [!] do not weaken theorem statements, physical assumptions, exact mass `33/20`, or decay rates to obtain compilation;
- [!] do not identify random-scan or heat-bath Markov time with geometric Euclidean time;
- [!] do not infer `L²` Poincare from total-variation Dobrushin control alone;
- [!] do not infer a volume-uniform gap from positivity at each finite volume;
- [!] do not promote the crossing-only gap to the full spatially sandwiched transfer without a theorem;
- [!] do not treat finite `Z₂` as compact `SU(2)` or `SU(N)`;
- [!] do not treat a supplied continuum construction spine as a constructed continuum model;
- [!] do not treat the beta-zero product theory as the interacting continuum theory;
- [!] do not treat `exactGapValueReal = 33/20` as a physical mass before normalization;
- [!] do not use open, Draft, stale, or superseded branches as authoritative theorem evidence;
- [!] do not replace a concrete model theorem by an opaque certificate whose fields restate the desired conclusion.

## Final definition of done

The project reaches its mathematical objective only when the authoritative carrier contains a replayable, concrete, non-circular chain

```text
finite Wilson gauge models
  -> actual geometric one-slab transfer
  -> volume-uniform quantitative gap
  -> nontrivial continuum Euclidean Yang--Mills measure
  -> reconstructed physical Hamiltonian
  -> strict positive physical spectral gap
```

with every model-specific assumption discharged by definitions and theorems for one explicit approximation family.
