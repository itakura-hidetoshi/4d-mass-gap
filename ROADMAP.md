# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-08-18 JST**.

It distinguishes:

- **Integrated** — merged into the authoritative theorem carrier;
- **Conditional route** — theorem machinery is integrated but still needs stated model-derived inputs;
- **Open** — a genuine theorem or model-facing construction is still required.

## Snapshot

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest theorem-bearing checkpoint:
  PR #1767
  Lift continuum rational finite reflection laws to full path invariance

theorem checkpoint merge SHA:
  b4196326db0b6d5d5e96bb55046a641aaffef9ea

checkpoint validation:
  PR Lean Fast Check #10809
  completed / success
```

Documentation-only merges may advance the carrier branch tip beyond the theorem checkpoint SHA without changing the theorem state represented by this roadmap.

## Roadmap in one view

```text
ACTUAL WILSON / CONTINUUM CONSTRUCTION LANE

actual periodic-even compact SU(N) Wilson Gibbs geometry           [Integrated]
  -> gauge-invariant plaquette / normalized-trace observables      [Integrated]
  -> integer temporal covariance + reflection geometry             [Integrated]
  -> factorial rational-time same-root path embedding              [Integrated]
  -> path-valued Prokhorov subsequence limit                        [Integrated]
  -> finite rational-cylinder reflection law                        [Integrated #1765]
  -> continuum finite rational-cylinder reflection law              [Integrated #1766]
  -> full rational-path reflection invariance                       [Integrated #1767]
  -> same-root rational positive-time OS reflection positivity      [OPEN NOW]
  -> instantiate OS reconstruction on the same-root continuum law   [OPEN]
  -> full 4D interacting continuum gauge-field construction         [OPEN]

PHYSICAL OS / HAMILTONIAN ANALYTIC LANE

physical OS correlation calculus                                  [Integrated]
  -> state-independent OS infrared mass                             [Integrated]
  -> graph-closed Hamiltonian comparison                            [Integrated]
  -> generator differential inequality + Mathlib Gronwall           [Integrated]
  -> full vacuum-orthogonal exponential norm decay                  [Integrated #1762]
  -> OS infrared mass = physicalYangMillsMass                       [Integrated #1763]
  -> physical mass = greatest full-sector uniform decay rate        [Integrated #1764]
  -> instantiate this analytic lane from the actual Wilson root     [OPEN]

SEPARATE FINITE-TO-CONTINUUM RATE LANE

intrinsic finite Wilson rate + canonical slow states               [Integrated machinery]
  -> selected moving-time o(a_n) residual                           [OPEN]
  -> intrinsic finite Wilson rate = physical mass                   [Conditional route]

EXACT-VALUE LANE

actual R4 component extrema + sharpness                            [OPEN]
  -> independent physical normalization                             [OPEN]
  -> physical interpretation of normalized 33/20 endpoint          [OPEN]
```

The immediate program frontier is **same-root continuum OS reflection positivity above the actual Wilson rational path construction**. Generic Hilbert-space infrastructure and full path reflection invariance are no longer the immediate blockers.

---

# Milestone ledger

## Milestone 0 — Authority, replay, and claim discipline

**Status: Integrated and permanent.**

Repository rules:

```text
start ordinary PRs from the exact authoritative SHA
start as Draft
use the GitHub connector as the canonical repository-operation path
judge CI only after workflow / job / Lean step is completed
do not write to a PR head while its CI is queued or in_progress
separate Lean/code failures from Actions/cache/external failures
keep development additive / tighten-only
never introduce sorry / admit / axiom / placeholder constants
fix the final head before Ready
re-check exact head / base / mergeability / reviews / threads before merge
integrate green PRs by normal merge with expected head pinned
record the new exact authoritative merge SHA
start the next Draft from that exact SHA.
```

The public `main` branch is a landing surface. The theorem authority is `formal/real-hilbert-uniform-coercive-strong-limit`.

---

## Milestone 1 — Continuum OS, Hilbert, semigroup, Hamiltonian, and spectral infrastructure

**Status: Integrated as theorem infrastructure.**

The repository formalizes

```text
reflection-positive quotients
real pre-Hilbert / Hilbert completion
positive-time contraction semigroups
strong continuity and right-generator domains
graph-closed Hamiltonians
self-adjointness interfaces
PVM / bounded-Borel spectral calculus
scalar spectral measures
vacuum-orthogonal Rayleigh / variational mass definitions.
```

Boundary: this infrastructure transports consequences from supplied OS data. It does not itself construct the interacting continuum Yang--Mills measure from the Wilson model.

---

## Milestone 2 — Actual finite compact `SU(N)` Wilson / OS geometry

**Status: Integrated.**

Integrated finite-model surfaces include:

```text
periodic-even compact SU(N) Wilson Gibbs probability
normalized Haar geometry
finite Wilson reflection positivity and OS Gram structure
completed finite OS Hilbert carriers
boundary-Haar and interacting-boundary L2 realizations
boundary-vacuum observables
actual-analysis / plaquette / cylinder observable layers
finite positive-half theorem bridges.
```

The interacting boundary law remains the actual Wilson marginal rather than being replaced by Haar measure at nonzero coupling.

---

## Milestone 3 — Actual finite Wilson positive-time theorem bridge

**Status: Integrated through PR #1670; concrete model instantiation remains downstream.**

PR #1670 integrates the reusable route

```text
actual finite Wilson strictness
  -> bounded-continuous plaquette/cylinder representatives
  -> canonical C0 -> L2 transport
  -> positive-time submodule / coherent pullback range interfaces
  -> reconstructed nonzero vacuum-orthogonal physical excitation
  -> Hamiltonian-domain / Rayleigh / physical-mass handoff.
```

Permanent anti-shortcuts:

```text
no global surjectivity of the coherent positive-half pullback
no global multiplicativity assumption
no abstract density inserted for the target actual mode
no duplicate physical Hilbert carrier
no identification A†A = Euclidean time evolution.
```

---

## Milestone 4 — Actual finite gauge invariance

**Status: Integrated.**

The actual periodic compact-gauge geometry proves covariance of oriented plaquette holonomies and conjugation invariance of the normalized real trace-power observables used downstream. Gauge invariance is theorem-generated from the finite model rather than supplied as a terminal premise for these observables.

---

## Milestone 5 — Integer temporal and reflection geometry

**Status: Integrated.**

The finite Wilson boundary-vacuum readout is promoted to an integer-time family by actual configuration translation. Exact temporal covariance and the finite configuration reflection law yield identities of the form

```text
Psi_t(R A) = Psi_{-t}(A)
```

with orientation corrections handled in the actual lattice geometry.

---

## Milestone 6 — Factorial rational-time path embedding

**Status: Integrated.**

The countable continuum carrier is

```text
PhysicalConfiguration := ℚ -> ℝ.
```

At lattice scale `n`, rational time `q` is represented by the established floor selector. The path measure is a pushforward of the **same actual finite Wilson Gibbs measure**.

Canonical factorial spacing supplies eventual exact lattice alignment for every fixed rational time and every fixed finite rational tuple.

Permanent arithmetic boundary:

```text
floor(-x) = -floor(x)
```

is not used in general. Oddness is used only after exact lattice alignment has been proved.

---

## Milestone 7 — Same-root path-valued Prokhorov continuum limit

**Status: Integrated.**

The rational path embedding lives in a countable product Polish carrier. Existing tightness/Prokhorov machinery extracts a convergent subsequence of the actual Wilson pushforward laws and constructs

```text
L.continuumMeasure : ProbabilityMeasure (ℚ -> ℝ).
```

The physical scaling subsequence remains cofinal.

Boundary: this is a continuum law of the selected boundary-vacuum observable skeleton, not yet the complete four-dimensional continuum gauge connection.

---

## Milestone 8 — Finite Wilson Gibbs reflection invariance

**Status: Integrated.**

The finite periodic `SU(N)` Wilson Gibbs measure is measure-preserving under the actual physical reflection through

```text
Haar/product reflection invariance
+
Wilson-action reflection invariance.
```

No finite-law reflection axiom is inserted.

---

## Milestone 9 — Finite rational-cylinder reflection laws

**Status: Integrated — PR #1765.**

For every fixed finite rational tuple, factorial spacing makes all insertion times simultaneously lattice-aligned at sufficiently large scale. Deterministic reflection covariance plus finite Wilson Gibbs reflection invariance then gives eventual exact equality

```text
law( x(-t_i) )_i = law( x(t_i) )_i
```

along every relevant strict Prokhorov subsequence.

---

## Milestone 10 — Continuum finite rational-cylinder reflection laws

**Status: Integrated — PR #1766.**

For every labelled finite rational tuple `time : Fin m -> ℚ`, Mathlib's continuous mapping theorem sends path-valued weak convergence to the reflected and unreflected finite-dimensional pushforwards.

Eventual exact equality of the finite laws and uniqueness of weak limits yield

```text
map (x ↦ fun i => x (-time i)) L.continuumMeasure
  =
map (x ↦ fun i => x ( time i)) L.continuumMeasure.
```

---

## Milestone 11 — Full continuum rational-path reflection invariance

**Status: Integrated — PR #1767.**

The `Fin m` theorem is reindexed to arbitrary finite index types and then to every finite subset of rational time. Mathlib's

```lean
ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
```

finite-dimensional-law uniqueness theorem closes the product-measure step:

```text
map θ L.continuumMeasure = L.continuumMeasure,
θ x q = x (-q).
```

Integrated exact merge SHA:

```text
b4196326db0b6d5d5e96bb55046a641aaffef9ea
```

Final PR validation:

```text
PR Lean Fast Check #10809
completed / success
```

This is geometric reflection invariance of the same-root continuum path law. It does **not** imply OS reflection positivity by itself.

---

# Immediate continuum OS frontier

## Milestone 12 — Same-root rational positive-time OS reflection positivity

**Status: OPEN — immediate principal frontier.**

For an appropriate positive-time rational cylinder observable `F`, construct the continuum reflection form from the actual same-root path law and prove

```text
0 <= reflectionForm(F).
```

Schematically,

```text
reflectionForm(F)
  = ∫ conj(F(θ x)) * F(x) dL.continuumMeasure(x).
```

The exact real/complex presentation should reuse the repository's existing OS conventions.

### Available integrated ingredients

```text
finite Wilson Gram / reflection positivity
actual finite Wilson Gibbs reflection geometry
integer temporal/reflection covariance
factorial rational-time alignment
same-root rational path embedding
path-valued weak convergence
continuum finite-cylinder reflection laws
full continuum path reflection invariance.
```

The generic reflection-limit interfaces can already turn pointwise convergence of finite reflection forms into continuum nonnegativity. The missing work is now model-facing identification and convergence.

### Required same-root construction

Preferred order:

```text
1. define positive rational-time cylinder observables on ℚ -> ℝ;
2. for each finite cylinder, choose the actual finite Wilson positive-half pullback;
3. use factorial alignment to identify its time slots exactly for all large n;
4. identify the finite cylinder reflection form with the existing finite Wilson OS/Gram form;
5. obtain finite nonnegativity from the existing theorem, not a new premise;
6. prove convergence of the finite reflection forms along the same Prokhorov subsequence;
7. instantiate the existing automatic reflection-limit positivity bridge;
8. conclude continuum rational-cylinder OS reflection positivity.
```

Finite prefixes are irrelevant to the limiting argument, so factorial alignment only needs to hold eventually.

### Anti-shortcuts

Do not:

```text
postulate continuum reflection positivity as a fresh axiom
infer positivity from reflection invariance alone
replace the same-root pullback by an unrelated continuum observable family
assume global positive-half surjectivity
assume global pullback multiplicativity
identify static Wilson Gram A†A with Euclidean time evolution.
```

---

## Milestone 13 — Same-root OS quotient/completion and physical reconstruction

**Status: OPEN as model instantiation; generic infrastructure integrated.**

After Milestone 12, instantiate the existing physical OS reconstruction on the same continuum law:

```text
same-root continuum reflection-positive cylinder algebra
  -> OS null quotient
  -> Hilbert completion
  -> positive-time contraction semigroup
  -> strong continuity
  -> graph-closed Hamiltonian
  -> vacuum / vacuum-orthogonal excitation sector.
```

The goal is to remove the current gap between the explicitly constructed Wilson continuum object and the conditional physical OS/Hamiltonian theorem interfaces.

---

# Integrated physical OS / Hamiltonian mass lane

## Milestone 14 — Physical OS correlation calculus and infrared mass

**Status: Integrated.**

The repository constructs physical OS autocorrelations, convexity/logarithmic-decay structures, long-time effective masses, and the state-independent variational OS infrared mass over nonzero vacuum-orthogonal states.

This is theorem infrastructure over physical OS data until Milestones 12–13 instantiate it from the same Wilson root.

---

## Milestone 15 — Graph-closed Hamiltonian comparison

**Status: Integrated.**

OS infrared lower bounds are transported through the canonical right-generator/right-Hamiltonian domain and graph closure to the graph-closed physical Hamiltonian Rayleigh infimum.

The reverse comparison is then derived from physical semigroup dynamics rather than postulated.

---

## Milestone 16 — Mathlib Gronwall and full-sector physical-mass decay

**Status: Integrated, including PR #1762 full-sector extension.**

The proof route is

```text
squared-orbit right derivative
  -> Hamiltonian Rayleigh lower bound
  -> real right-neighborhood slope
  -> Mathlib scalar Gronwall
  -> generator-domain exponential norm decay
  -> time-average density / closure
  -> all ψ ⟂ Ω.
```

Result:

```text
‖T_t ψ‖ <= ‖ψ‖ * exp (-physicalYangMillsMass * t).
```

No spectral theorem, spectral-attainment premise, numerical mass value, or extra identity `T_t = exp(-tH)` is required for this derivation.

---

## Milestone 17 — OS infrared mass equals physical Hamiltonian mass

**Status: Integrated — PR #1763.**

The authoritative carrier proves

```text
physicalYangMillsOSInfraredMass = physicalYangMillsMass.
```

This equality is currently a theorem of the physical OS/Hamiltonian interfaces under their explicit hypotheses. Milestones 12–13 are required to instantiate it from the explicit same-root Wilson continuum law.

---

## Milestone 18 — Physical mass as the optimal uniform decay rate

**Status: Integrated — PR #1764.**

A real rate `r` is a full vacuum-orthogonal uniform exponential rate when

```text
forall t >= 0, forall ψ ⟂ Ω,
  ‖T_t ψ‖ <= ‖ψ‖ * exp (-r * t).
```

A `Set.IsGreatest` theorem proves that `physicalYangMillsMass` is an attained greatest element of this set.

Thus the analytic lane identifies

```text
graph-closed Hamiltonian variational mass
=
physical OS infrared mass
=
optimal full-sector uniform exponential decay rate.
```

---

# Separate finite-to-continuum dynamical lane

## Milestone 19 — Intrinsic finite Wilson rates and canonical slow states

**Status: Integrated as theorem machinery.**

The repository retains the intrinsic finite Wilson rate

```text
g_n = -log ‖T_n^exc‖ / a_n
```

and theorem-generated two-step slow states. The continuum symmetric-semigroup side contains the moving Rayleigh recovery machinery needed for a reverse variational limit.

---

## Milestone 20 — Selected moving-time residual

**Status: OPEN.**

For the selected finite slow states `phi_n`, prove

```text
‖ iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ‖
  <= 2 a_n delta_n,

delta_n -> 0.
```

Equivalently, the residual is `o(a_n)`.

Ordinary fixed-time convergence is not a substitute for this moving-time comparison.

The integrated OS infrared/Hamiltonian mass equality does not automatically prove convergence of the intrinsic finite Wilson rates.

---

## Milestone 21 — Intrinsic finite Wilson rate = physical mass

**Status: Conditional route; actual quantitative closure open.**

Once Milestone 20 and the required common physical realization are discharged, the existing forward/reverse variational machinery can identify the finite Wilson intrinsic rate limit with `physicalYangMillsMass`.

This remains logically separate from the already integrated OS infrared equality.

---

# Full interacting continuum Yang--Mills lane

## Milestone 22 — Extend beyond the rational boundary-vacuum skeleton

**Status: OPEN.**

The rational path law is a concrete same-root continuum observable construction. A complete four-dimensional Yang--Mills construction still requires a sufficiently rich continuum gauge-field/state object carrying the physical local observable content.

The extension must remain anchored to the actual finite Wilson root rather than introducing an independent continuum theory by assumption.

---

## Milestone 23 — Full continuum Euclidean / gauge / regularity package

**Status: OPEN.**

The final model must construct, in the formulation required by the existing interfaces,

```text
four-dimensional Euclidean covariance
gauge covariance / gauge-invariant observable content
reflection positivity
regularity / temperedness or the chosen formal substitute
clustering / vacuum structure
finite-Wilson compatibility
physical time-semigroup realization.
```

These must be model-derived rather than retained as terminal data.

---

## Milestone 24 — Nontriviality and physical excitation from the same root

**Status: OPEN as final model integration.**

The finite Wilson actual-analysis / positive-time theorem bridge already contains strong reusable machinery. The remaining task is to identify its concrete continuum positive-time observables with the same-root OS-positive construction and obtain nontrivial vacuum-orthogonal states in the final continuum physical theory.

---

# Exact-value and physical-normalization lane

## Milestone 25 — Actual R4 decomposition and component extrema

**Status: Structural theorem route integrated; model-derived numerical values open.**

Still required:

```text
derive the actual physical component decomposition
prove the necessary form/domain bounds
evaluate the relevant component Rayleigh extrema
prove sharp combined-budget attainment or an equivalent sharpness theorem.
```

No coefficient may be assigned merely to manufacture the target rational number.

---

## Milestone 26 — Independent physical normalization and `33/20`

**Status: Conditional exact-value assembly integrated; physical interpretation open.**

The repository retains the normalized endpoint

```text
33/20.
```

A physical statement involving this value requires independent proofs of

```text
actual physical mass identification
actual model-derived component extrema
sharpness
physical reference-time / unit normalization.
```

Only then may a relation such as

```text
referenceTime * physicalYangMillsMass = 33/20
```

be interpreted physically.

---

## Milestone 27 — Final physical Yang--Mills existence and mass-gap theorem

**Status: OPEN.**

A final theorem must begin from the actual interacting four-dimensional compact-gauge Yang--Mills construction and conclude a nontrivial reconstructed physical Hilbert theory with a strictly positive non-vacuum spectral lower bound for the physical Hamiltonian.

It must not depend circularly on an assumed exact mass value.

Permanent numerical distinctions:

```text
finite Z2 geometric cap / coercivity 1/2
  != intrinsic compact-Wilson finite rate
  != physicalYangMillsMass
  != normalized conditional endpoint 33/20.
```

---

# Immediate next proof package

The safest additive order from theorem checkpoint `b4196326db0b6d5d5e96bb55046a641aaffef9ea` is:

```text
1. define the same-root positive rational-time cylinder algebra;
2. construct its actual finite Wilson positive-half pullbacks;
3. prove exact aligned readout identities for every fixed finite cylinder;
4. rewrite the finite cylinder reflection form as the established finite Wilson OS/Gram form;
5. obtain finite nonnegativity from the existing Wilson reflection-positivity theorem;
6. prove convergence of the reflection forms along the same Prokhorov subsequence;
7. instantiate the existing automatic reflection-limit positivity interface;
8. conclude continuum rational-cylinder OS reflection positivity;
9. connect that same-root OS-positive law to the existing physical reconstruction;
10. reuse the integrated mass = IR mass = optimal decay theorem on the actual model.
```

The preferred proof style is to reuse Mathlib and the already-constructed finite Wilson geometry instead of adding a new wrapper or a stronger physical hypothesis.

# Anti-goals

Do not:

- claim the Clay Millennium problem is solved before the full model-facing construction is complete;
- infer OS reflection positivity from the now-integrated reflection invariance theorem;
- identify the rational scalar boundary-vacuum path with the complete continuum gauge field;
- replace the actual Wilson same-root continuum law by an unrelated abstract continuum measure;
- assume global positive-half pullback surjectivity or multiplicativity;
- identify static finite Wilson Gram operators with Euclidean time evolution;
- replace the selected moving-time `o(a_n)` condition by fixed-time convergence;
- identify finite `Z₂` coercivity `1/2` with the physical compact-gauge mass;
- interpret `33/20` physically before the independent model-derived extrema and unit normalization are proved.

# Completion criterion for the program

The program is complete only when a single theorem chain begins from an actual interacting four-dimensional compact-gauge Yang--Mills construction and reaches the reconstructed physical Hamiltonian with a strictly positive non-vacuum spectral gap, with all required continuum OS, gauge, Euclidean, regularity, nontriviality, finite-Wilson compatibility, and normalization inputs constructed rather than merely supplied.
