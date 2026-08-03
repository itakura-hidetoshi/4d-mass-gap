# MGAP4D Roadmap

This document records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

It distinguishes:

- theorem infrastructure already replayed on the active carrier;
- finite-volume Wilson / heat-bath / boundary-transfer results now integrated;
- current temporal/geometric OS comparison results;
- remaining model-specific bridge obligations; and
- results that are explicitly not claimed.

## Snapshot — 2026-08-03 JST

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #1365 — Construct shifted geometric Wilson OS kernel operator semigroup

fixed integrated PR head:
  9d275aee4cfaf8c0a056b8e17c466cbc45b9dee5

latest integrated carrier / squash merge:
  4600dc1488a0b80576d247075ce2afdafd48edfa

latest integrated validation:
  PR Lean Fast Check #8625
  run id 30780128446
  completed / success

post-merge comparison:
  4600dc1488a0b80576d247075ce2afdafd48edfa
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

This roadmap supersedes the 2026-07-16 snapshot that stopped at PR #906 and Draft PR #907.

## Status notation

- `[x]` — integrated and replayed on the authoritative carrier.
- `[>]` — immediate active theorem unit.
- `[~]` — active Draft work; not yet an authoritative fact.
- `[ ]` — open.
- “conditional theorem route integrated” means that the theorem from the stated input is proved; the input remains separately open.

A theorem parametrized by a construction spine does not construct the spine.  A finite heat-bath theorem does not automatically identify heat-bath time with Euclidean OS time.  A beta-zero closure theorem does not automatically give a nonzero-coupling continuum trajectory.  A geometric one-layer reflection form that realizes only its own matrix elements does not by itself produce a nontrivial transfer operator.

---

## Proof architecture

The repository now has four connected but distinct lanes.

```text
A. OS / PVM / Hamiltonian / exact-spectrum lane

Euclidean observables and measures
  -> reflection-positive OS quotient and completion
  -> physical Hilbert space and vacuum
  -> strongly continuous semigroup
  -> self-adjoint Hamiltonian interface
  -> constructed bounded-Borel PVM calculus
  -> reconstructed spectral support
  -> exact lower-spectrum consequences from a supplied construction spine
  -> concrete continuum construction and spectral transfer [open]


B. explicit finite periodic SU(N) Wilson L2/coercivity lane

compact-Haar one-link conditional laws
  -> explicit periodic Dobrushin matrix
  -> native Gibbs variance and Dirichlet identities
  -> conditional finite Schur/Poincare generator
  -> common-coefficient finite Gibbs L2 Poincare/coercivity
  -> reflected-integral / vacuum-decay / continuum common-carrier route
  -> tail-uniform nonzero-coupling finite-volume estimates [open]


C. finite Wilson boundary-analysis and heat-bath dynamics lane

boundary Haar L2
  -> measure-geometric Haar-to-Gibbs analysis isometry
  -> canonical adjoint synthesis
  -> centered heat-bath exponential from coercivity
  -> full heat-bath semigroup and boundary Hamiltonian
  -> generator leakage defect
  -> second-moment leakage curvature
  -> beta-zero sharp boundary closure
  -> nonzero-beta boundary/OS moment intertwining [open]


D. temporal/geometric OS comparison lane

geometric Wilson one-layer form
  -> random-scan temporal OS transfer comparison
  -> beta-zero boundary heat-bath comparison
  -> exact two-defect no-go/realization theorems
  -> one-layer Hilbert completion identity obstruction
  -> independent shifted-kernel quotient/completion/semigroup
  -> actual shifted geometric kernel from Wilson geometry [open]
```

The lanes meet only after a concrete approximation family supplies both finite quantitative estimates and a continuum OS/Hamiltonian limit with compatible operator, form, or semigroup convergence.

---

## Milestone 1 — preserve the formal finite, continuum, OS, and spectral backbone

Status: **integrated theorem infrastructure**

- [x] finite Wilson Gibbs probability and conditional-law infrastructure;
- [x] finite heat-bath Hilbert-space and Hamiltonian theorem generators;
- [x] weak-limit, OS reconstruction, semigroup, generator, Hamiltonian, and spectral interfaces;
- [x] R4 gauge-field, gauge-action, gauge-invariant observable, Schwinger, correlation, and reflection-positive surfaces;
- [x] quotient, section, transport, pre-Hilbert, and completed real Hilbert-space routes;
- [x] stable public theorem surfaces for downstream exact-spectrum statements;
- [x] explicit separation of theorem packages, physical instantiation, and final Yang--Mills claims.

Definition of done:

The repository retains a replayable formal backbone without treating conditional package fields or normalized internal spectral data as an unconditional physical construction.

---

## Milestone 2 — exact lower-spectrum theorem chain

Status: **integrated**

For every supplied

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

- [x] prove `HasHamiltonianMassGap` at `exactGapValueReal`;
- [x] prove the spectrum lies in `{0} ∪ [exactGapValueReal,∞)`;
- [x] prove the open interval below the threshold is spectrally empty;
- [x] prove threshold attainment;
- [x] prove leastness and the nonzero-spectrum infimum identity;
- [x] classify the spectrum below and at the exact threshold;
- [x] identify the first excitation with `exactGapValueReal`;
- [x] prove uniqueness of the least nonzero spectral energy.

Boundary:

This milestone derives consequences from a supplied spine.  It does not construct a concrete interacting four-dimensional gauge family that supplies the spine.

---

## Milestone 3 — reconstructed support, bounded-Borel PVM calculus, and physical graph route

Status: **integrated**

- [x] identify scalar spectral support with the non-vacuum exact-gap core spectrum;
- [x] identify pure PVM open support with the same spectrum;
- [x] characterize the threshold by support membership, leastness, and support infimum;
- [x] preserve compatibility with continuous spectrum at threshold;
- [x] construct canonical simple-function PVM integration;
- [x] complete bounded Borel multipliers in operator norm;
- [x] prove zero, one, indicator, subtraction, real-scalar, symmetry, polarization, and multiplicativity laws;
- [x] construct quadratic scalar spectral measures;
- [x] expose the restricted Hamiltonian with self-adjointness, dense domain, and closedness;
- [x] derive physical semigroup compatibility, PVM difference quotients, coordinate graph identities, strong continuity, and graph closure from explicit inputs.

Definition of done:

The spectral-support and functional-calculus objects consumed by the physical semigroup route are theorem-generated from the reconstructed PVM rather than stored as independent algebraic fields.

---

## Milestone 4 — explicit periodic compact-Haar `SU(N)` Wilson influence and native variance system

Status: **integrated**

- [x] specialize the compact-Haar heat-bath Hilbert space to periodic `SU(N)` Wilson systems;
- [x] expose the normalized Haar--Gibbs vacuum and nonnegative heat-bath form;
- [x] prove the exact random-scan/heat-bath operator identity;
- [x] restrict periodic geometry to the nondegenerate tail `n >= 3`;
- [x] localize conditional changes to shared plaquettes;
- [x] derive mutual normalized Haar-density domination;
- [x] derive the bounded-test influence coefficient;
- [x] prove active-neighbor support and volume-independent row/column bounds;
- [x] prove finite Schur `l2` matrix estimates;
- [x] prove one-link variation propagation;
- [x] prove random-scan `l1` and squared-`l2` variation contraction;
- [x] prove native Gibbs variance and heat-bath Dirichlet identities;
- [x] reduce finite Poincare/coercivity generation to explicit profile/Rayleigh inputs.

Explicit coefficient surface:

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta

strict bounded-test contraction region:
  beta < log (19 / 17) / 4
```

Boundary:

Observable oscillation contraction is not automatically a full Gibbs `L²` Poincare theorem.  The later packages keep the `L²` Rayleigh/coercivity input explicit unless it has been theorem-generated.

---

## Milestone 5 — finite reflected-integral, vacuum-decay, and boundary-transfer route

Status: **integrated through PRs #1348–#1352**

This milestone moves the downstream finite-to-continuum path from a broad physical assumption to typed finite Hilbert-space transfer packages.

- [x] prove the round trip between completed nonnegative vacuum norm decay and actual finite periodic `SU(N)` Wilson reflected-integral decay;
- [x] route shared-boundary `L²` Poincare defect estimates to finite reflected-integral decay;
- [x] route exponential boundary-transfer operator-norm contraction through Dobrushin-rate endpoints;
- [x] distinguish shared-boundary Haar `L²` and compact Wilson Gibbs `L²` as different Hilbert carriers;
- [x] factor boundary transfer as

```text
boundarySynthesis ∘ gibbsEvolution ∘ boundaryAnalysis;
```

- [x] replace one bundled transfer bound by separate analysis, Gibbs-evolution, and synthesis estimates;
- [x] preserve finite reflected-integral decay, completed vacuum decay, continuum right-Hamiltonian coercivity, graph-closed coercivity, and normalized-vacuum kernel uniqueness with the same mass parameter.

Boundary:

The compact heat-bath or random-scan Hamiltonian is not identified with OS Euclidean-time translation.  The actual boundary/OS moment intertwining remains a separate model-specific theorem.

---

## Milestone 6 — canonical boundary analysis and finite heat-bath dynamics

Status: **integrated through PRs #1353–#1362**

This milestone replaces arbitrary boundary maps and opaque evolution factors by concrete canonical finite Wilson objects.

- [x] construct centered finite Gibbs heat-bath evolution by explicit vacuum projection;
- [x] generate boundary synthesis as the real Hilbert adjoint of one analysis isometry;
- [x] derive centered heat-bath exponential decay from finite heat-bath coercivity;
- [x] construct a boundary Haar-to-Gibbs analysis isometry from boundary projection and inverse-square-root density transport;
- [x] construct the OS-compatible boundary marginal vacuum isometry;
- [x] compress the actual centered heat-bath evolution through canonical analysis and adjoint synthesis;
- [x] construct the canonical boundary heat-bath Hamiltonian and quadratic-form package;
- [x] construct the full compact Wilson heat-bath semigroup package;
- [x] identify exact generator leakage defect `D_HB = H_HB A - A H_boundary`;
- [x] identify positive second-moment leakage curvature and prove `Q = 0 ↔ D = 0`;
- [x] close beta-zero canonical boundary normalization, generator invariance, sharp Poincare/coercivity constant one, zero-mode exclusion, all-real-time compressed semigroup, intertwining, continuity, and derivative.

Boundary:

The beta-zero closure is exact for the actual finite-volume periodic-even Wilson system at `beta = 0`.  It does not assert nonzero-coupling range invariance, nonzero-coupling geometric OS time, or a continuum Yang--Mills Hamiltonian.

---

## Milestone 7 — temporal OS, geometric OS, and heat-bath comparison defects

Status: **integrated through PRs #1363–#1365**

This milestone prevents a false identification of three different dynamics.

### PR #1363 — two-defect comparison package

- [x] construct generic real-Hilbert discrete semigroup comparison defects;
- [x] construct the geometric Wilson one-layer transfer form from the reflection certificate;
- [x] classify the random-scan temporal OS semigroup as powers of its one-step path shift;
- [x] sample the beta-zero boundary heat-bath family at arbitrary real spacing;
- [x] define the matrix defect and heat-bath bridge defect;
- [x] prove exact no-go theorems from a witness in either defect;
- [x] expose a canonical two-defect terminal package.

### PR #1364 — one-layer geometric OS Hilbert completion and identity obstruction

- [x] complete the one-layer Wilson reflection form as an OS Hilbert space;
- [x] prove its inner product is exactly the Wilson one-layer form;
- [x] prove that a bounded candidate reproducing all one-layer matrix elements must be the identity transfer;
- [x] prove that nonidentity candidates have explicit nonzero matrix-element witnesses;
- [x] compare the identity transfer with the beta-zero heat-bath step through an explicit bridge defect;
- [x] prove simultaneous realization iff candidate is identity and the beta-zero heat-bath step is identity.

### PR #1365 — independent shifted geometric kernel semigroup

- [x] define an independent shifted-kernel bilinear form on positive-half configurations;
- [x] require explicit raw carrier realization, contraction, OS symmetry, and positivity;
- [x] prove contraction preserves the OS-null submodule;
- [x] descend the shifted operator through separation quotient and Hilbert completion;
- [x] prove completed contraction, symmetry, positivity, and exact dense matrix elements;
- [x] construct a discrete natural-time shifted semigroup and its iterated matrix elements;
- [x] compare shifted and unshifted reflection forms by exact defects;
- [x] prove equality with the unshifted form forces identity;
- [x] prove beta-zero boundary bridge classifications and terminal no-go dichotomies.

Boundary:

A shifted kernel is independent input.  It is not inferred from the unshifted reflection form.  Random-scan Markov time and finite heat-bath time are not renamed as geometric Wilson Euclidean time.

---

## Current frontier — model-specific bridges

Status: **open**

The downstream spectral and finite-to-continuum packaging is now substantially theorem-generated.  The remaining work is concentrated in concrete model construction and compatibility.

- [ ] construct or certify a genuinely shifted geometric Wilson OS kernel from actual finite Wilson translation geometry;
- [ ] prove exact boundary/OS moment intertwining for the constructed canonical boundary analysis map and the actual finite heat-bath or temporal OS evolution;
- [ ] extend the beta-zero analyzed-range and semigroup closure to the required nonzero-coupling regime, or prove the exact obstruction;
- [ ] obtain tail-uniform finite-volume `L²` coercivity/gap estimates compatible with the continuum scaling route;
- [ ] construct the continuum Yang--Mills OS/Hamiltonian spine rather than supplying it as a parameter;
- [ ] transfer finite coercivity to a nontrivial continuum Hamiltonian without confusing finite heat-bath time, random-scan time, and OS Euclidean time;
- [ ] externally audit the final physical normalization, scale, and claim boundary before any public Clay-style theorem statement.

Anti-goals:

- do not weaken theorem statements, mass values, decay factors, or physical assumptions;
- do not claim an unconditional Clay solution from a supplied construction spine;
- do not promote bounded-test total-variation contraction to full Gibbs `L²` coercivity without the required certificate;
- do not identify one-layer reflection-form identity transfer with nontrivial Euclidean time;
- do not treat beta-zero closure as a nonzero-coupling continuum theorem;
- do not introduce untracked spectral convergence, Riesz projection convergence, root convergence, or eigenvalue enumeration.

---

## Practical next PR candidates

1. **Actual shifted-kernel construction package.**  Build an explicit candidate shifted Wilson kernel from finite geometry and prove the certificate fields required by the PR #1365 package.
2. **Nonzero-beta boundary defect package.**  Compute the canonical boundary generator defect beyond beta zero and classify whether it vanishes, is small, or gives a hard obstruction.
3. **Boundary/OS moment intertwining package.**  Connect canonical boundary analysis to the finite OS translation moments without identifying carriers definitionally.
4. **Tail-uniform coercivity package.**  Isolate the exact finite-volume hypotheses needed to pass from common finite Gibbs gaps to continuum Hamiltonian coercivity.
5. **Construction-spine instantiation package.**  Replace supplied continuum-spine fields by theorem-generated data from the finite approximation family.

The preferred order is to close bridge theorems before adding downstream wrappers: first produce the actual kernel/defect/intertwining data, then route it through the already integrated spectral and continuum endpoints.
