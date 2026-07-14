# MGAP4D Roadmap

This roadmap records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-14 JST

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #843 — Prove compact-Haar random-scan variation contraction

latest integrated PR head:
  7d017f297b9b35ab5f88945edc88391dc57ab53d

latest integrated merge commit:
  8138a2fb7ef84794feb40f4d651efa947de34894

latest validation:
  PR Lean Fast Check run #6085
  run id 29305474231
  success

post-merge comparison:
  8138a2fb7ef84794feb40f4d651efa947de34894
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical
```

The repository now has two converging proof lanes:

```text
A. reconstructed OS/PVM/Hamiltonian lane
   Euclidean observables and measure
     -> OS physical Hilbert space
     -> strong semigroup continuity
     -> self-adjoint Hamiltonian
     -> constructed bounded-Borel PVM calculus
     -> canonical coordinate graph
     -> exact spectral-support and exact-gap endpoints

B. explicit finite periodic SU(N) Wilson lane
   compact-Haar one-link conditionals
     -> explicit Dobrushin influence matrix
     -> strict volume-independent coefficient
     -> symmetric row/column control and Schur estimate
     -> actual observable variation propagation
     -> random-scan variation contraction
     -> Gibbs L² approximate tensorization [open]
     -> tail-uniform finite-volume coercivity [open at the analytic input]
     -> continuum coercivity transfer [open]
```

The immediate mathematical frontier is the bridge from the explicit observable variation theory of PRs #841–#843 to the native Gibbs `L²` conditional-variance form. The final frontier remains construction of a nontrivial four-dimensional continuum Yang--Mills theory along a physically relevant scaling family and transfer of a positive lower spectral bound to its reconstructed Hamiltonian.

## Status notation

- `[x]` means integrated and replayed on the active proof carrier.
- `[>]` means the next active theorem unit.
- `[ ]` means open or not yet physically instantiated.
- A conditional theorem package is marked integrated only as a theorem from its stated inputs; its unresolved input remains separately open.

A merged theorem parametrized by a construction spine does not prove that a concrete physical family supplies that spine. A finite-volume gap theorem does not prove that the same lower bound survives a continuum scaling limit. A small-coupling Dobrushin region is not automatically the four-dimensional weak-coupling continuum trajectory.

---

## Milestone 1 — preserve finite, continuum, OS, and exact-spectrum foundations

Status: **integrated theorem infrastructure**

- [x] finite Wilson Gibbs probability and conditional-law infrastructure;
- [x] finite heat-bath Hilbert and Hamiltonian theorem generators;
- [x] conditional weak-limit, OS reconstruction, Hamiltonian, resolvent, graph-limit, and spectral-interface packages;
- [x] R4 gauge-field, gauge-action, gauge-invariant, Schwinger, correlation, and reflection-positive reconstruction surfaces;
- [x] quotient, section, transport, pre-Hilbert, and completed real Hilbert-space route;
- [x] completed OS semigroup, generator, Hamiltonian, and self-adjoint `LinearPMap` operator APIs;
- [x] direct bare-`M` bounded operator route and complete-construction direct bounded certificate;
- [x] stable downstream and public-consumer theorem surfaces;
- [x] preserve the distinction between formal theorem packages, physical instantiation, and a final Yang--Mills theorem.

Definition of done:

The repository retains a replayable formal backbone without treating conditional packages or normalized internal values as an unconditional physical result.

---

## Milestone 2 — exact lower-spectrum theorem chain

Status: **integrated by PRs #744–#746**

For every supplied

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

- [x] prove `HasHamiltonianMassGap` at `exactGapValueReal`;
- [x] prove the spectrum lies in `{0} ∪ [exactGapValueReal,∞)`;
- [x] prove the open interval `(0, exactGapValueReal)` is spectrally empty;
- [x] prove exact-gap attainment;
- [x] prove leastness and the nonzero-spectrum infimum identity;
- [x] classify the full spectrum below and at the exact threshold;
- [x] identify the model first excitation with `exactGapValueReal`;
- [x] prove uniqueness of the least nonzero spectral energy;
- [x] retain exact-gap interval, threshold-separation, and first-excitation certificate surfaces.

Primary surfaces:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate
EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate
EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate
```

Definition of done:

Every supplied complete construction spine has a formally classified lower spectrum with an attained unique first nonzero energy.

Boundary:

This milestone does not construct the complete physical spine or derive its exact-gap fields from a concrete gauge approximation family.

---

## Milestone 3 — replace abstract spectral support by reconstructed support

Status: **integrated through PR #782**

- [x] connect the explicit Wightman/OS exact-gap core to scalar spectral support;
- [x] identify scalar support with the non-vacuum exact-gap core spectrum;
- [x] prove exact-gap support membership, leastness, and support-infimum identity without a singleton PVM eigenprojection;
- [x] connect the same exact-gap core to the pure open-neighborhood support of the actual bounded PVM on `Ω⊥`;
- [x] identify pure PVM open support with the non-vacuum exact-gap core spectrum;
- [x] retain the canonical restricted Hamiltonian with self-adjointness, dense domain, and closedness;
- [x] remove scalar-measure realization choices from the final pure-PVM support endpoint.

Key checkpoints:

```text
PR #781 — Connect exact-gap core to continuous spectral support
PR #782 — Connect exact-gap core to pure PVM open support
```

Definition of done:

The exact threshold is detected by the support of the actual reconstructed spectral object, including continuous-spectrum-compatible formulations, rather than only by an abstract spectrum field.

---

## Milestone 4 — construct the bounded-Borel PVM calculus

Status: **integrated through PR #820**

- [x] construct canonical simple-function PVM integration;
- [x] prove presentation invariance under common refinements;
- [x] construct uniform simple approximation of bounded Borel real functions;
- [x] complete the simple integrals in operator norm;
- [x] prove zero, one, measurable-indicator, subtraction, and real-scalar laws;
- [x] prove the completed indicator law recovers the PVM projection;
- [x] prove one-Lipschitz continuity in uniform norm;
- [x] construct the quadratic scalar spectral measure from actual PVM countable additivity;
- [x] prove scalar and projection tail continuity;
- [x] prove quadratic-form integral identities;
- [x] prove inner symmetry of the completed integral;
- [x] prove real-Hilbert polarization for symmetric bounded operators;
- [x] prove simple-function multiplicativity;
- [x] lift multiplicativity to all bounded Borel multipliers.

Key checkpoints:

```text
PR #803 — algebraic laws for bounded-Borel PVM integration
PRs #804–#814 — restriction, coordinate, compact-tail, and physical derivative interfaces
PRs #815–#820 — positive support, quadratic forms, polarization, and multiplicativity
```

Definition of done:

The PVM functional calculus consumed by the physical semigroup route is a theorem-generated algebra of bounded operators, not a collection of assumed algebraic fields.

---

## Milestone 5 — identify the physical semigroup and Hamiltonian coordinate graph

Status: **integrated through PR #829**

- [x] prove positive PVM support from the exact-gap support route;
- [x] identify the positive Euclidean semigroup with the bounded PVM exponential operator;
- [x] prove the physical PVM difference-quotient formula;
- [x] derive the canonical restricted PVM coordinate graph;
- [x] derive the physical generator from a strong-continuity core;
- [x] reduce all-vector strong continuity to represented Euclidean observable states plus density and contractivity;
- [x] prove the OS physical-state map is an isometry on the observable norm;
- [x] derive observable-norm continuity from dominated convergence of the actual Euclidean realization integrands;
- [x] transport observable continuity to strong continuity on the completed Hilbert space;
- [x] derive Hamiltonian-domain right derivatives from an observable graph core;
- [x] replace coordinatewise graph closure assumptions by Hamiltonian graph-norm density;
- [x] derive the required graph estimate from a contractive generator-average factorization.

Key checkpoints:

```text
PR #821 — identify T_t with the PVM exponential
PR #822 — derive the physical PVM difference quotient
PR #823 — derive the canonical coordinate graph from gap data
PRs #824–#827 — derive strong continuity from OS observable data
PRs #828–#829 — derive Hamiltonian-domain derivatives from graph-norm core data
```

Definition of done:

The reconstructed Hamiltonian/PVM compatibility is connected to actual Euclidean measure, observable, OS exchange, density, and graph-core data. Full-Hilbert continuity and Hamiltonian-domain differentiation are not left as opaque independent package fields.

Remaining boundary:

This lane still depends on a physical continuum model and its gap/support inputs. It reduces dependency opacity; it does not independently create a nontrivial four-dimensional continuum theory.

---

## Milestone 6 — connect the genuine periodic `SU(N)` Wilson system to heat-bath gap data

Status: **integrated theorem route through PR #838; quantitative analytic input not yet discharged**

- [x] specialize the compact-Haar heat-bath Hilbert space and Hamiltonian to periodic `SU(N)` Wilson systems;
- [x] expose the normalized Haar--Gibbs vacuum, nonnegative form, and vacuum-orthogonal coercivity consequence of a Poincaré inequality;
- [x] formulate scale-uniform and tail-uniform heat-bath gap data;
- [x] derive uniform finite-scale coercivity from a family of strict Dobrushin/random-scan certificates;
- [x] isolate the finite-scale centered random-scan `L²` Rayleigh estimate as the remaining analytic input;
- [x] prove the exact Gibbs `L²` operator identity

```text
P_scan = I - |Edge|⁻¹ H_HB;
```

- [x] prove equivalence between the centered random-scan Rayleigh estimate and the native heat-bath Poincaré inequality;
- [x] restrict the explicit periodic geometry to the nondegenerate tail `n ≥ 3` rather than imposing artificial claims at `n = 1,2`.

Key checkpoints:

```text
PR #830 — periodic SU(N) compact-Haar heat-bath bridge
PR #831 — family Dobrushin-to-uniform-gap bridge
PR #836 — explicit finite gap package with one centered L² input
PR #837 — genuine Gibbs L² random-scan operator structure
PR #838 — tail-uniform periodic SU(N) gap package
```

Definition of done:

The exact analytic theorem that would generate the finite-volume `SU(N)` Poincaré constant is isolated on the genuine Gibbs Hilbert space, and all downstream finite Hamiltonian consequences follow from it.

Unfinished input:

The centered random-scan `L²` Rayleigh estimate has not yet been derived from the explicit Wilson interaction.

---

## Milestone 7 — derive the explicit periodic `SU(N)` Dobrushin matrix

Status: **integrated through PR #840**

- [x] define compact-oriented plaquette/link incidence and shared-plaquette sets;
- [x] prove Wilson plaquette energy is insensitive to replacements outside its four physical links;
- [x] localize source-response oscillation exactly to target/source shared plaquettes;
- [x] prove the logarithmic conditional-weight oscillation bound;
- [x] convert oscillation control into mutual normalized Haar-density domination;
- [x] prove the sharp bounded-test influence estimate from mutual density domination;
- [x] define the explicit off-diagonal influence coefficient;
- [x] identify the periodic compact-oriented shared-plaquette set with the coordinate geometric set;
- [x] prove every active neighbor shares exactly one plaquette for side length `n ≥ 3`;
- [x] prove exact support of the influence matrix on active neighbors;
- [x] prove the volume-independent row-sum estimate

```text
row sum <= 18 * eta_beta,
eta_beta = (exp (4 * beta) - 1) / (exp (4 * beta) + 1);
```

- [x] prove strict contraction under

```text
beta < log (19 / 17) / 4;
```

- [x] prove symmetry of the periodic shared-plaquette influence matrix;
- [x] obtain the same volume-independent column bound;
- [x] prove `ℓ¹` contraction for nonnegative finite link profiles.

Key checkpoints:

```text
PR #832 — shared-plaquette oscillation localization
PR #833 — normalized Haar conditional-density comparison
PR #834 — sharp bounded-test influence coefficient
PR #835 — strict periodic SU(N) Dobrushin matrix
PR #840 — symmetry, column control, and ℓ¹ profile contraction
```

Definition of done:

The actual non-Abelian periodic Wilson interaction generates a concrete symmetric finite Dobrushin matrix with an explicit volume-independent strict coefficient in the proved parameter region.

---

## Milestone 8 — observable variation and finite matrix contraction

Status: **integrated through PR #843**

- [x] prove a reusable weighted Cauchy--Schwarz estimate for a nonnegative finite matrix row;
- [x] expose the periodic `SU(N)` influence as a finite real matrix;
- [x] combine row and column bounds into the Schur estimate

```text
sum_target (sum_source c target source * v source)^2
  <= (18 * eta_beta)^2 * sum_source (v source)^2;
```

- [x] define exact compact-Haar one-link conditional expectations on bounded continuous observables;
- [x] define proof-relevant link-variation and centered fiber-variation profiles;
- [x] prove one-link conditional expectation kills the resampled target variation;
- [x] prove one-link Dobrushin propagation

```text
variation_source (P_target O)
  <= variation_source O
     + influence target source * variation_target O;
```

- [x] define the actual uniform random-scan average of one-link conditional expectations;
- [x] prove the exact finite-sum variation update formula;
- [x] prove one target update decreases total variation by at least

```text
(1 - coefficient) * variation_target;
```

- [x] prove random-scan `ℓ¹` total-variation contraction at rate

```text
1 - (1 - coefficient) / |Edge|.
```

Key checkpoints:

```text
PR #841 — periodic SU(N) Schur ℓ² contraction
PR #842 — one-link observable variation propagation
PR #843 — actual random-scan observable variation contraction
```

Definition of done:

The explicit Dobrushin matrix now acts on genuine bounded gauge observables rather than only on abstract profile vectors, and the actual random-scan observable has a proved volume-normalized `ℓ¹` contraction.

---

## Milestone 9 — close Gibbs `L²` approximate tensorization

Status: **immediate active mathematical frontier**

- [>] define the squared link-variation energy naturally associated with the PR #842 centered variation profile;
- [ ] combine the one-link update formula with the symmetric matrix and PR #841 Schur estimate to prove a random-scan `ℓ²` variation-energy contraction;
- [ ] prove the required comparison between pointwise/fiber variation energy and the actual Haar--Gibbs single-link conditional variance;
- [ ] formulate and prove the finite Gibbs approximate-tensorization inequality;
- [ ] derive the centered random-scan `L²` Rayleigh estimate used by PR #836;
- [ ] use

```text
P_scan = I - |Edge|⁻¹ H_HB
```

to obtain the native heat-bath Poincaré inequality;
- [ ] instantiate the tail-uniform periodic `SU(N)` gap package of PR #838 without an externally supplied scale-wise Rayleigh field;
- [ ] prove tail-uniform vacuum-orthogonal coercivity and zero-kernel uniqueness from the explicit Wilson interaction alone within the proved Dobrushin regime.

Preferred theorem order:

```text
finite squared-profile Schur update
  -> observable random-scan squared variation bound
  -> conditional-variance comparison
  -> approximate tensorization
  -> centered random-scan Rayleigh
  -> heat-bath Poincaré
  -> tail-uniform finite Hamiltonian gap.
```

Definition of done:

The genuine periodic compact-Haar `SU(N)` Wilson interaction, with no independent `L²` Rayleigh or Poincaré assumption, generates one positive tail-uniform finite-volume heat-bath gap in the explicit strict Dobrushin region.

Anti-goal:

Do not replace this analytic theorem by another package field, receipt, alias, or constructor that merely renames the centered Rayleigh estimate.

---

## Milestone 10 — transfer finite-volume coercivity into the continuum OS Hamiltonian

Status: **open after Milestone 9**

- [ ] choose a concrete sequence of periodic `SU(N)` Wilson systems and a continuum scaling parameterization;
- [ ] connect the tail-uniform finite Hilbert spaces and Hamiltonians to the existing OS continuum approximation spine;
- [ ] prove compatibility of vacuum centering and vacuum-orthogonal sectors along the approximation maps;
- [ ] prove the required strong, resolvent, form, or graph convergence of the finite Hamiltonians;
- [ ] prove that the common finite lower bound survives the selected limit mode;
- [ ] exclude collapse of the non-vacuum sector or loss of the lower spectral estimate in the limit;
- [ ] identify the limiting lower bound with the reconstructed continuum Hamiltonian spectrum;
- [ ] connect the resulting continuum coercivity theorem to the exact-gap support and PVM coordinate-graph route.

Definition of done:

A specified continuum reconstruction receives a positive Hamiltonian lower bound from theorem-generated finite `SU(N)` coercivity rather than from a supplied continuum spectral certificate.

Key mathematical warning:

Uniform finite gaps do not pass automatically through an arbitrary weak measure limit. The proof must specify the operator/form convergence and the vacuum-sector identifications that preserve coercivity.

---

## Milestone 11 — reconcile the Dobrushin region with physical continuum scaling

Status: **fundamental open physical/analytic frontier**

- [ ] state unambiguously the convention for `beta`, lattice spacing, bare coupling, and group rank;
- [ ] determine the scaling trajectory required for the intended four-dimensional continuum Yang--Mills theory;
- [ ] prove whether the current strict condition

```text
beta < log (19 / 17) / 4
```

can hold along that trajectory;
- [ ] if it cannot, extend the finite-gap method beyond the current small-`beta` Dobrushin region or replace it with another quantitative mechanism;
- [ ] avoid identifying a strong-coupling lattice gap with a weak-coupling continuum mass gap without a theorem connecting the regimes;
- [ ] preserve explicit dependence on lattice size, physical volume, coupling, and normalization throughout the transfer.

Definition of done:

The finite quantitative gap mechanism applies along the same approximation family used to construct the claimed four-dimensional continuum theory.

This milestone is logically independent of completing the finite `L²` estimate: both are required.

---

## Milestone 12 — construct a concrete nontrivial continuum Yang--Mills spine

Status: **decisive open construction frontier**

- [ ] fix the compact gauge group and one concrete approximation family;
- [ ] specify boundary conditions, lattice sequence, interpolation maps, observable algebra, and physical-volume scaling;
- [ ] prove gauge invariance and finite-volume consistency;
- [ ] prove tightness, compactness, or another continuum-existence mechanism;
- [ ] prove nontriviality of the continuum limit;
- [ ] prove Euclidean covariance and reflection positivity for the limiting Schwinger family;
- [ ] prove the required connected-correlation nondegeneracy from explicit gauge-invariant observables;
- [ ] construct the physical Hilbert space, vacuum, semigroup, generator, and Hamiltonian from that family;
- [ ] construct the spectral PVM and support from the resulting Hamiltonian;
- [ ] replace every remaining supplied field of `EuclideanYangMillsContinuumMeasureConstructionSpine` by a theorem from the chosen family;
- [ ] instantiate the exact-spectrum theorem chain with the resulting construction.

Definition of done:

One concrete approximation family supplies the complete OS/Hamiltonian/PVM construction spine and its nontriviality data without importing the desired continuum spectral conclusion as a field.

---

## Milestone 13 — physical normalization and exact mass-gap identification

Status: **open**

- [ ] separate dimensionless lattice and internal theorem normalizations from a physical mass scale;
- [ ] explain and prove the role of the internal `33/20` provenance route in the physical model;
- [ ] identify the continuum Hamiltonian units and renormalization convention;
- [ ] prove that the lower spectral value obtained from finite-to-continuum transfer is positive in physical units;
- [ ] determine whether the physical gap is exactly `exactGapValueReal` or whether that public endpoint must be reparameterized;
- [ ] prove that the continuum theory is interacting and not a trivial or Gaussian limit;
- [ ] state the gauge group and theorem scope without hidden generalization.

Definition of done:

The exact-gap value in the final theorem has a derived mathematical and physical interpretation in the instantiated continuum theory.

---

## Milestone 14 — final theorem and independent review

Status: **not claimed**

- [ ] assemble one replayable theorem path from the explicit approximation family to the final existence and mass-gap statement;
- [ ] document every hypothesis and dependency;
- [ ] ensure no essential physical conclusion is stored as an input field;
- [ ] replay the complete Lean dependency path from a fresh clone;
- [ ] obtain independent expert review of the mathematical argument and formalization;
- [ ] reconcile the result with the precise Clay problem statement;
- [ ] only then consider unconditional final-theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume coercivity, conditional continuum packages, supplied spectral certificates, internal normalization, or formal replay with construction of the physical four-dimensional Yang--Mills theory itself.

## Current priority order

```text
1. prove random-scan ℓ² variation-energy contraction from PRs #841–#843;
2. prove the Gibbs conditional-variance / approximate-tensorization bridge;
3. close the centered random-scan Rayleigh and native heat-bath Poincaré theorem;
4. instantiate the tail-uniform periodic SU(N) finite gap from the explicit Wilson interaction;
5. define and prove the finite-to-continuum coercivity transfer;
6. resolve the small-beta versus continuum-scaling regime boundary;
7. complete the nontrivial continuum OS construction;
8. connect the resulting Hamiltonian support to the exact-gap endpoint;
9. perform independent mathematical review before any final claim.
```

Additional wrappers, aliases, smoke files, receipts, and handoff structures are secondary. They are justified only when they expose an actual dependency, eliminate a supplied theorem field, stabilize a theorem surface used by the next proof, or connect the explicit finite interaction to the continuum Hamiltonian.

## Non-claims at the current checkpoint

The active carrier does not yet establish:

```text
a Gibbs L² approximate-tensorization theorem from the current variation profiles;
an unconditional periodic SU(N) heat-bath gap generated solely from the explicit interaction;
transfer of that gap to a continuum OS Hamiltonian;
compatibility of the current strict Dobrushin region with the physical continuum scaling trajectory;
a complete nontrivial interacting four-dimensional continuum Yang-Mills construction;
a physical derivation of exactGapValueReal or 33/20 from that family;
an unconditional Clay Millennium Yang-Mills existence and mass-gap theorem;
independent external mathematical consensus.
```

The integrated results are substantial formal progress: the reconstructed PVM and semigroup route has been made markedly less assumptive, and the actual periodic non-Abelian Wilson interaction now reaches explicit Dobrushin matrices and genuine observable random-scan variation contraction. The next decisive progress must be an analytic theorem connecting those variations to the Gibbs `L²` form and then a physically valid finite-to-continuum transfer.
