# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

The active development is intentionally proof-boundary preserving.  The repository separates:

1. an Osterwalder--Schrader / Hilbert-space / Hamiltonian / spectral lane;
2. an explicit finite periodic compact-Haar `SU(N)` Wilson / heat-bath / coercivity lane;
3. a finite Wilson boundary-analysis / heat-bath dynamics / OS comparison lane; and
4. the still-open model-specific bridges needed before a continuum Yang--Mills mass-gap theorem can be claimed.

The integrated Lean packages are substantial formal components of a possible proof route.  They do **not** yet constitute an unconditional construction of four-dimensional Yang--Mills theory or a proof of the Clay Millennium problem.

```text
Canonical repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Detailed development plan:
  ROADMAP.md

KuuOS reference bridge:
  docs/kuuos_reference_bridge.md
```

## Authoritative status — 2026-08-03 JST

### Latest integrated checkpoint

```text
PR:
  #1365 — Construct shifted geometric Wilson OS kernel operator semigroup

fixed PR head:
  9d275aee4cfaf8c0a056b8e17c466cbc45b9dee5

authoritative carrier / squash merge:
  4600dc1488a0b80576d247075ce2afdafd48edfa

validation:
  PR Lean Fast Check #8625
  run id 30780128446
  completed / success

post-merge comparison:
  4600dc1488a0b80576d247075ce2afdafd48edfa
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical / ahead 0 / behind 0
```

This replaces the older documentation snapshot that stopped at PR #906 / Draft PR #907.

### Current public boundary

The active carrier now contains a completed sequence through:

```text
exact spectral consequences from a supplied construction spine
  -> reconstructed PVM / bounded-Borel calculus / physical semigroup graph
  -> compact-Haar finite Wilson Dobrushin and native Gibbs L2 infrastructure
  -> finite Gibbs Poincare/coercivity and reflected-integral/vacuum equivalences
  -> shared-boundary L2 transfer and Dobrushin-rate boundary contraction interfaces
  -> canonical boundary Haar/Gibbs analysis isometries and boundary marginal vacuum transport
  -> centered and full finite Wilson heat-bath semigroup packages
  -> boundary heat-bath Hamiltonian, generator-defect, leakage-curvature, and beta-zero closure
  -> two-defect comparison of geometric Wilson form, random-scan temporal OS transfer, and beta-zero heat-bath time
  -> geometric OS Hilbert completion identity obstruction
  -> independent shifted-kernel quotient/completion/semigroup comparison package.
```

The main theorem boundary is now more precise than in the previous README:

- the downstream OS / spectral / continuum coercivity route is theorem-generated once its model-specific finite and continuum inputs are supplied;
- finite Gibbs `L²` Poincare/coercivity has been connected to boundary-transfer, finite reflected-integral, vacuum-decay, and continuum common-carrier endpoints;
- the canonical boundary analysis map has been constructed from measure geometry in several important cases;
- the beta-zero canonical boundary heat-bath semigroup is closed sharply on its own finite boundary carrier;
- the currently available one-layer Wilson reflection form completes to the identity transfer, so it cannot by itself be a nontrivial geometric Euclidean-time transfer;
- a nontrivial geometric time transfer requires additional shifted-kernel data or an explicit bridge theorem, not a relabeling of random-scan or heat-bath time.

## Executive summary

The repository now has three mature theorem layers and one genuine frontier.

### 1. Exact-spectrum reconstruction layer

For every supplied

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

write

```lean
sigma := S.definitionBridge.spine.model.energySpectrum
Delta := exactGapValueReal
E1 := S.definitionBridge.spine.model.firstExcitation
```

The active carrier proves consequences including:

```lean
HasHamiltonianMassGap sigma Delta
sigma ⊆ ({0} : Set ℝ) ∪ Set.Ici Delta
Set.Ioo 0 Delta ∩ sigma = ∅
Delta ∈ sigma
IsLeast (sigma \ ({0} : Set ℝ)) Delta
sInf (sigma \ ({0} : Set ℝ)) = Delta
sigma ∩ Set.Iio Delta = ({0} : Set ℝ)
(sigma \ ({0} : Set ℝ)) ∩ Set.Iic Delta = ({Delta} : Set ℝ)
sigma ∩ Set.Iic Delta = ({0, Delta} : Set ℝ)
E1 = Delta
∃! E : ℝ, IsLeast (sigma \ ({0} : Set ℝ)) E
```

These are theorems from the fields of the supplied construction spine.  They do not by themselves construct that spine from a concrete four-dimensional gauge approximation family.

### 2. Finite Wilson `L²` coercivity and transfer layer

The finite periodic compact-Haar Wilson lane is based on

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

and contains exact one-link conditional laws, Dobrushin coefficients, native Gibbs variance identities, finite Schur/Poincare theorem generators, and finite Gibbs heat-bath coercivity packages.

The strict coefficient region still contains the explicit bounded-test influence constants

```text
eta_beta   = (exp (4 * beta) - 1) / (exp (4 * beta) + 1)
alpha_beta = 18 * eta_beta

strict bounded-test contraction region:
  beta < log (19 / 17) / 4
```

Later packages route finite Gibbs `L²` Poincare/coercivity through shared-boundary `L²` transfer, reflected-integral decay, completed vacuum decay, continuum common-carrier coercivity, graph-closed coercivity, and normalized-vacuum kernel uniqueness.  Total-variation Dobrushin control is not treated as a free `L²` theorem; the `L²` Rayleigh/coercivity inputs remain explicit theorem data where required.

### 3. Boundary analysis and heat-bath dynamics layer

The recent carrier constructs and separates:

```text
shared-boundary Haar L2
  -> finite Wilson Gibbs L2
  -> finite Wilson Gibbs heat-bath evolution
  -> shared-boundary Haar L2
```

through canonical analysis and synthesis maps, with synthesis generated as the real Hilbert adjoint once the analysis isometry is fixed.

Integrated results include:

- centered Gibbs heat-bath evolution by explicit vacuum projection;
- derivation of centered heat-bath exponential decay from finite heat-bath coercivity;
- measure-geometric boundary Haar-to-Gibbs analysis isometries;
- boundary marginal vacuum normalization;
- canonical boundary compressed heat-bath evolution;
- boundary heat-bath Hamiltonian and quadratic-form packages;
- full finite Wilson heat-bath semigroup packages;
- exact generator leakage defects;
- positive second-moment leakage curvature;
- beta-zero boundary normalization, sharp coercivity constant one, zero-mode exclusion, and all-real-time compressed semigroup closure.

The beta-zero package is exact and sharp, but it is a beta-zero finite-boundary theorem.  It is not a nonzero-coupling continuum construction.

### 4. Temporal OS / geometric OS / heat-bath comparison layer

The latest packages explicitly separate three dynamics:

```text
geometric Wilson one-layer OS kernel/form
random-scan stationary-path temporal OS transfer
canonical beta-zero boundary heat-bath evolution
```

The carrier now proves exact comparison-defect theorems.  In particular:

- the geometric one-layer Wilson reflection form completes to a Hilbert space whose canonical matrix-element realization is the identity transfer;
- every candidate reproducing the same one-layer matrix elements on the dense observable image is uniquely the identity;
- a nonidentity heat-bath step gives an exact obstruction to simultaneous one-layer/heat-bath realization;
- an independent shifted geometric kernel can be quotiented, completed, and exponentiated as a natural-time semigroup when supplied with an explicit certificate;
- equality of the shifted kernel with the unshifted reflection form again forces identity, so genuinely nontrivial geometric Euclidean time requires genuinely shifted-kernel data.

Random-scan Markov time, finite heat-bath time, and geometric Wilson Euclidean time are not identified by notation.

## What is not claimed

The active carrier does **not** claim any of the following as closed facts:

- an unconditional Clay Millennium Yang--Mills mass-gap proof;
- a concrete nontrivial four-dimensional continuum Yang--Mills construction spine generated from finite periodic `SU(N)` systems;
- a nonzero-beta continuum scaling trajectory with a proven tail-uniform physical gap;
- identification of finite heat-bath/random-scan dynamics with geometric OS Euclidean-time translation without an explicit bridge theorem;
- derivation of a nontrivial geometric transfer from the unshifted one-layer reflection form alone;
- a nonzero-coupling version of the beta-zero boundary semigroup closure;
- promotion of bounded-test total-variation contraction to full Gibbs `L²` coercivity without the required `L²` certificate;
- weakening of theorem statements, physical assumptions, mass values, or decay rates.

## Current mathematical frontier

The next proof work is concentrated on the model-specific bridges rather than on downstream spectral packaging:

1. construct or certify a genuinely shifted geometric Wilson OS kernel from actual finite Wilson geometry;
2. prove exact boundary/OS moment intertwining for the constructed canonical boundary analysis map and the actual heat-bath or temporal OS evolution;
3. extend the beta-zero boundary closure to the relevant nonzero-coupling regime, or isolate the exact obstruction;
4. produce tail-uniform finite-volume estimates compatible with a continuum OS/Hamiltonian limit;
5. instantiate the supplied continuum construction spine rather than assuming it as data.

Once the appropriate finite and continuum bridge data are supplied, the integrated theorem packages route them to finite reflected-integral decay, completed vacuum decay, continuum coercivity, exact spectral lower-bound consequences, and normalized-vacuum kernel statements.
