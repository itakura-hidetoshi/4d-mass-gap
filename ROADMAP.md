# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-08-15 JST**.

It distinguishes:

- **Integrated** — merged into the authoritative theorem carrier;
- **Draft-proved** — present on the active Draft PR and Lean-checked there, but not yet authoritative;
- **Open** — a genuine model-facing theorem or construction still required.

## Snapshot

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

authoritative head:
  7fb099ddc94275f0b0832d98aefc25bc5a699196

latest integrated checkpoint:
  PR #1669
  Lift full positive-boundary Wilson Fock strictness to the actual analysis sector

active Draft:
  PR #1670
  Lift actual Wilson strictness to a reconstructed physical excitation

active Draft branch:
  formal/actual-wilson-os-physical-excitation-v1
```

Open or Draft work is not part of the authoritative theorem state until it is integrated.

## Roadmap in one line

```text
actual finite Wilson strictness in actual analysis                 [Integrated #1669]
  -> actual plaquette algebra + raw C0 closure                    [Draft-proved #1670]
  -> positive-time pullback / L2 range factorization              [Draft-proved #1670]
  -> actual finite positive-time realization                       [OPEN NOW]
  -> reconstructed nonzero physical excitation / domain witness   [Draft downstream]
  -> selected moving-time o(a_n) recovery                          [OPEN]
  -> intrinsic Wilson rate = physical mass                         [conditional theorem route]
  -> actual interacting continuum Yang--Mills construction         [OPEN]
  -> actual R4 extrema + independent normalization                 [OPEN]
  -> final physical mass-gap theorem                               [OPEN]
```

## Current architecture

The program now has six logically distinct lanes.

### A. Continuum OS / Hamiltonian / spectral infrastructure

```text
reflection positivity
  -> separated OS quotient
  -> real Hilbert completion
  -> symmetric contraction semigroup
  -> graph-closed physical Hamiltonian
  -> PVM / bounded-Borel calculus
  -> variational physical mass.
```

**Status: Integrated as theorem infrastructure.**

### B. Actual finite compact Wilson / OS analysis

```text
periodic-even compact Wilson Gibbs law
  -> finite reflection positivity
  -> completed finite OS Hilbert carrier
  -> boundary-moment / boundary-Haar L2 realization
  -> interacting boundary marginal m0^2 dHaar
  -> positive-boundary Fock / Gram strictness
  -> actual boundary analysis and raw actual-analysis modes.
```

**Status: Integrated through PR #1669.**

### C. Actual finite Wilson positive-time realization

```text
actual plaquette algebra
  -> C0 closure of raw actual-analysis modes
  -> coherent positive-half pullback range
  -> open-half Haar L2 range
  -> reconstructed physical excitation.
```

**Status: active Draft #1670; one concrete realization step remains open.**

### D. Finite-to-continuum dynamical recovery

```text
finite Wilson intrinsic rate g_n
  -> theorem-generated slow states phi_n
  -> moving-time comparison at 2 a_n
  -> continuum Rayleigh limsup
  -> reverse physical-mass inequality
  -> intrinsic-rate / physical-mass equality.
```

**Status: theorem machinery integrated; selected moving-time residual open.**

### E. Global continuum/common-carrier construction

```text
interacting boundary common product
  -> common-product physical realization
  -> physical Hilbert infinite-dimensionality / strict OS family
  -> global finite-to-continuum ambient carrier.
```

**Status: generic reductions integrated; concrete global realization still open.**

### F. Physical exact-value / normalization lane

```text
actual physical component forms
  -> component Rayleigh extrema
  -> sharp R4 budget
  -> actual physical mass identification
  -> independent reference-time normalization
  -> normalized 33/20 endpoint.
```

**Status: structural theorem route integrated conditionally; model-derived numerical inputs open.**

---

# Milestone ledger

## Milestone 0 — Authority, replay, and claim discipline

**Status: Integrated and permanent.**

Repository rules:

```text
start ordinary PRs from the exact authoritative SHA
start as Draft
fix final head before Ready
use completed run/job/step/artifact/log evidence for CI conclusions
never treat queued/in_progress as final evidence
do not write to a branch while its CI is running
separate Lean/code failures from Actions/cache/external failures
re-audit base/head/mergeability/reviews/threads before merge
squash merge only
pin expected_head_sha at merge
verify the authoritative carrier after integration.
```

The public `main` branch is a landing surface. The theorem authority is `formal/real-hilbert-uniform-coercive-strong-limit`.

## Milestone 1 — Continuum OS, Hilbert, semigroup, Hamiltonian, and PVM infrastructure

**Status: Integrated.**

The repository contains the abstract and analytic infrastructure needed to pass from reflection-positive Euclidean data to a completed real physical Hilbert space, a physical time semigroup, graph-closed Hamiltonian interfaces, spectral measures, and variational mass statements.

Boundary: this does not itself construct interacting continuum Yang--Mills.

## Milestone 2 — Actual finite compact `SU(N)` Wilson / OS geometry

**Status: Integrated.**

Integrated surfaces include:

```text
finite periodic Wilson Gibbs probability
compact Haar geometry
reflection-positive finite Wilson forms
completed finite OS Hilbert spaces
boundary-moment realization in boundary-Haar L2
interacting boundary marginal m0^2 dHaar
reciprocal-vacuum density correction
selected finite/projective observation and boundary recovery.
```

The finite OS Hilbert carrier is identified with the exact range of the relevant realization maps, not with an arbitrary whole raw `L²` carrier.

## Milestone 3 — Finite `Z₂` geometric-transfer theorem

**Status: Integrated supporting lane.**

The finite `Z₂` model proves the genuine geometric transfer cap and coercivity constant

```text
1/2.
```

Permanent distinction:

```text
finite Z2 coercivity 1/2
  != compact SU(2)/SU(N) physical mass
  != normalized exact-value constant 33/20.
```

## Milestone 4 — Intrinsic finite Wilson rate, slow states, and moving Rayleigh machinery

**Status: Integrated as theorem infrastructure.**

The repository defines

```text
g_n = -log ||T_n^exc|| / a_n
```

and theorem-generates finite two-step slow states without assuming exact norm attainment or one-step positivity. The continuum semigroup side contains the time-average and moving Rayleigh estimates needed for reverse variational recovery.

## Milestone 5 — Global common-product and strict-Gram reductions

**Status: Integrated as generic reductions; concrete realization open downstream.**

The interacting boundary marginals generate a countable common product and canonical finite OS embeddings. The existence of a common-product physical isometry is reduced through Hilbert geometry to physical infinite-dimensionality, then to independent separated OS classes, then to finite positive-definite reflected OS Gram matrices.

The earlier #1602 strict-Gram reduction remains valid infrastructure. It is no longer the immediate local frontier of the active #1670 construction.

## Milestone 6 — PR #1669: actual positive-boundary strictness to actual analysis

**Status: Integrated — current authoritative checkpoint.**

PR #1669 closes a large actual finite Wilson package including:

```text
positive-boundary temporal Wilson factorization
protected strict Wilson/Fock Gram structure
nonzero actual boundary analysis operator
interacting-boundary inverse L2 density transport
positive-density normalized-trace witnesses
open-half nonzero probes
factorized actual-analysis nonzero criteria
Hilbert-Schmidt / Gram convergence
strict centered actual-analysis output infrastructure.
```

This is the correct launch point for the current physical positive-time realization work.

---

# Active Draft #1670

## Milestone 7 — Actual plaquette algebra and raw actual-analysis `C⁰` closure

**Status: Draft-proved.**

A concrete actual plaquette algebra is built on the finite positive open-half configuration space. The explicit normalized-trace-polynomial raw actual-analysis continuous representative satisfies

```text
g_raw ∈ closure(actualPlaquetteAlgebraBoundedCarrier).
```

The approximation is generated from the actual Wilson/plaquette construction, completed-positive Gram-feature continuity, finite polynomial closure, and the boundary Bochner integral.

No abstract density hypothesis is needed for this target-specific closure theorem.

## Milestone 8 — Canonical `C⁰ -> L²` and positive-time-submodule factorization

**Status: Draft-proved.**

Mathlib's canonical bounded-continuous `toLp` map sends the raw `C⁰` representative to the actual open-half Haar `L²` mode.

The OS carrier wrapper is then removed by proving the canonical linear equivalence

```text
OS carrier ≃ₗ positive-time submodule.
```

Consequently the carrier-level and positive-time-submodule `L²` maps have identical ranges.

## Milestone 9 — Finite positive-half range equality and trace-power readout equivalence

**Status: Draft-proved.**

The finite positive-half observable range is identified exactly with the coherent positive-half pullback range:

```text
range(finitePositiveHalfObservable_n)
  = range(Q.positiveHalfPullback n).
```

The normalized-trace-power readout is then shown to be only a packaging of concrete finite range statements:

```text
Nonempty(readout Q n)
  <->
forall j,
  rawTracePowerBoundedFunction(n,j)
    ∈ range(finitePositiveHalfObservable_n).
```

This removes the appearance of an additional readout assumption.

## Milestone 10 — Actual finite positive-time realization

**Status: OPEN — immediate local frontier.**

There are two closely related formulations.

### Closure formulation

Prove

```text
actualPlaquetteAlgebraBoundedCarrier(halfExtent n)
  ⊆ range(Q.positiveHalfPullback n).
```

Then the already-proved `C⁰` closure gives

```text
g_raw ∈ closure(range(Q.positiveHalfPullback n)),
```

which is transported canonically to the positive-time open-half Haar `L²` range closure.

### Target-specific exact-range formulation

For every required normalized trace power `j`, prove

```text
rawTracePowerBoundedFunction(n,j)
  ∈ range(finitePositiveHalfObservable_n).
```

Then the readout/equivalence layer supplies exact positive-time `L²` range membership for the finite trace-power family and its polynomial combinations.

### Required proof style

Construct the necessary observables from the existing actual finite Wilson/projective/cylinder geometry.

Do **not** assume:

```text
global surjectivity of Q.positiveHalfPullback
global multiplicativity of Q.positiveHalfPullback
abstract Dense of the entire open-half bounded-continuous space
a duplicate physical Hilbert space
A†A = Euclidean time evolution.
```

Because the downstream pullback is deliberately exposed only as a linear map, products should be realized at the actual cylinder/positive-time observable level and their pointwise finite readouts proved explicitly. Multiplicativity of the pullback must not be inferred without a theorem.

## Milestone 11 — Reconstructed nonzero physical excitation and domain/Rayleigh handoff

**Status: downstream Draft theorem route ready; depends on Milestone 10.**

Once the local positive-time realization is supplied, the existing #1670 chain produces the relevant positive-time `L²` realization, a nonzero vacuum-orthogonal reconstructed state, Hamiltonian-domain witnesses under the existing semigroup/self-adjointness inputs, and the established Rayleigh / physical-mass consequences.

This milestone does not identify the static Wilson Gram operator with the physical Hamiltonian.

---

# Dynamical and global continuum milestones

## Milestone 12 — Selected slow-state moving-time residual

**Status: OPEN — principal dynamical frontier.**

For the canonical theorem-generated finite slow states `phi_n`, prove

```text
|| iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ||
  <= 2 a_n delta_n,

delta_n -> 0.
```

Equivalently, the residual is `o(a_n)`.

The estimate should come from genuine quantitative finite-to-continuum semigroup comparison, Mosco/Trotter--Kato style control, or another model-derived argument specialized to the selected sequence.

Do not replace it with ordinary fixed-time convergence.

## Milestone 13 — Intrinsic Wilson rate equals physical mass

**Status: conditional theorem route integrated; actual closure open.**

The forward and reverse variational theorem infrastructure is already present. Once the required ambient realization and Milestone 12 are discharged, theorem composition yields

```text
C.limit = physicalYangMillsMass.
```

This equality is not currently advertised as an unconditional theorem of the bare interacting compact Wilson model.

## Milestone 14 — Global common-product physical realization / strict continuum OS family

**Status: OPEN as a separate global kinematic lane.**

The older global reduction remains relevant whenever the full common-product physical isometry is required:

```text
concrete countable positive-time continuum observables
  -> every finite reflected OS Gram matrix is positive definite
  -> separated OS classes are linearly independent
  -> physical Hilbert is infinite-dimensional
  -> common-product physical isometry is theorem-generated.
```

The local #1670 finite-Wilson positive-time lift can produce a concrete excitation route, but it does not by itself assert the full global common-product realization.

## Milestone 15 — Interacting continuum Yang--Mills construction

**Status: OPEN.**

The final model must construct, rather than retain as terminal data, the appropriate continuum objects and properties, including as needed:

```text
nontrivial interacting continuum probability/state
gauge covariance / gauge content
reflection positivity
regularity / temperedness
clustering and/or vacuum uniqueness inputs
compatibility with finite Wilson approximants
physical time-semigroup identification.
```

This is indispensable for a final Clay-level claim.

---

# Exact-value and physical-normalization milestones

## Milestone 16 — Actual R4 decomposition and component variational extrema

**Status: structural theorem layer integrated; model-derived values open.**

For actual physical component forms, the repository identifies canonical coefficients with genuine Rayleigh-set `sInf` / `sSup` extrema.

Still required:

```text
derive the final component decomposition from the actual model
prove all required form/domain bounds
evaluate the six component extrema
prove sharp budget attainment or an equivalent sharpness theorem.
```

No coefficient may be set merely to manufacture the target rational number.

## Milestone 17 — Independent physical normalization and the `33/20` endpoint

**Status: conditional theorem assembly integrated; physical derivation open.**

The normalized exact-value route retains the target

```text
33/20.
```

A physical identity involving that value requires all of the following to be independently established:

```text
actual physical mass equality
actual model-derived R4 extrema
sharp combined budget
physical referenceTime / unit normalization.
```

Only then may an identity of the form

```text
referenceTime * physicalYangMillsMass = 33/20
```

be interpreted physically.

## Milestone 18 — Final physical Yang--Mills mass-gap theorem

**Status: OPEN.**

A final theorem must start from the actual interacting continuum Yang--Mills construction and conclude a strict non-vacuum spectral lower bound for the reconstructed physical Hamiltonian without circular numerical input.

It must preserve the distinctions

```text
finite Z2 cap 1/2
  != finite compact-Wilson intrinsic rate
  != continuum defect coercivity
  != physicalYangMillsMass
  != normalized 33/20 endpoint.
```

---

# Immediate next proof package

The safest additive next package is **actual positive-time finite-Wilson realization**, not another generic wrapper.

Preferred target order:

```text
1. identify the actual finite plaquette / normalized-trace-power cylinder observables;
2. construct corresponding physical positive-time observables from the existing projective/cylinder API;
3. prove exact pointwise finite readout identities;
4. package the closure-form plaquette lift and/or target-specific trace-power range facts;
5. invoke the already-proved #1670 C0/L2/range machinery;
6. obtain the reconstructed nonzero physical excitation and domain/Rayleigh consequences.
```

The proof should remain additive: do not weaken existing theorem statements, exact-value data, decay hypotheses, finite coercivity `1/2`, moving-time requirements, determinant conditions, or projective-coherence conditions.

# Anti-goals

Do not:

- claim the Clay Millennium problem is solved before the model-facing construction is complete;
- identify finite `Z₂` with compact `SU(2)` / `SU(N)` continuum Yang--Mills;
- identify the finite `1/2` transfer/coercivity constant with the physical Yang--Mills mass;
- identify interacting boundary marginals with Haar measure at nonzero coupling;
- assert exact cross-scale projectivity of interacting Wilson Gibbs laws without a theorem;
- identify a completed finite OS Hilbert space with a whole raw `L²` space when only an exact range is proved;
- promote reflection-positive semidefiniteness to strict positive definiteness without a strictness theorem;
- assume global surjectivity or multiplicativity of the coherent positive-half pullback;
- replace the selected moving-time `o(a_n)` residual by fixed-time convergence;
- insert exact finite eigenvectors or norm attainment when operator-norm approximation suffices;
- set R4 coefficients or `referenceTime` to force `33/20`;
- present `33/20` as an already-derived physical mass in fixed units.

# Definition of completion

The present program is complete only when one theorem chain constructs, rather than assumes, the needed physical data:

```text
actual finite compact Wilson approximants
+ actual finite positive-time realizability
+ interacting continuum OS Yang--Mills model
+ physical Hilbert / semigroup / Hamiltonian identification
+ selected moving-time finite-to-continuum recovery
+ intrinsic Wilson rate / physical-mass equality
+ strict positive non-vacuum spectral lower bound
+ actual R4 decomposition and extrema
+ independent physical normalization
```

and then concludes the intended physical mass-gap statement without circular certificates or numerical input.
