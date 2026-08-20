# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-08-20 JST**.

It replaces the older roadmap whose principal frontier was continuum OS reflection positivity. That frontier has now been crossed on the canonical same-root primary-scalar continuum process. The immediate mathematical frontier is a **strictly positive coercive lower bound on the exact same-root vacuum-orthogonal graph-closed Hamiltonian domain**.

## Status legend

- **Integrated** — merged into the authoritative theorem carrier.
- **Integrated infrastructure** — reusable theorem machinery is merged, but a separate model-facing instantiation is still required.
- **Open now** — the immediate constructive theorem target.
- **Open downstream** — required later, but not the next local blocker.
- **Conditional route** — theorem assembly exists only under explicit inputs that are not yet derived from the final model.

## Snapshot

```text
authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest theorem-bearing checkpoint:
  PR #1896
  formal: normalize the same-root OS vacuum and center the excitation semigroup

canonical exact merge SHA:
  777e48e54b1bdb8028d624513568be476a415e1d

checkpoint validation:
  PR Lean Fast Check #11202
  completed / success
```

The public `main` branch is a landing surface. The theorem authority is `formal/real-hilbert-uniform-coercive-strong-limit`.

## Roadmap in one view

```text
SAME-ROOT WILSON -> SCALAR CONTINUUM -> OS HAMILTONIAN LANE

actual periodic-even compact SU(N) Wilson Gibbs geometry            [Integrated]
  -> theorem-generated finite Wilson OS positivity                  [Integrated]
  -> one-sided primary reflection-fixed boundary readout            [Integrated]
  -> reflection-completed rational path                             [Integrated]
  -> canonical primary plaquette scalarization                      [Integrated]
  -> same-root Prokhorov continuum law on ℚ -> ℝ                   [Integrated]
  -> continuum positive rational-cylinder OS positivity             [Integrated #1802]
  -> intrinsic continuum reflection invariance                      [Integrated #1803]
  -> fixed-slot positive-semidefinite OS bilinear forms             [Integrated #1804]
  -> OS separation quotient / fixed-slot Hilbert completion         [Integrated]
  -> Hilbert directed system / algebraic direct limit               [Integrated]
  -> rational-time OS contraction                                   [Integrated #1845]
  -> completed rational contraction semigroup                       [Integrated]
  -> zero-time regular sector / real orbit extension                [Integrated #1884]
  -> real strongly continuous contraction semigroup                 [Integrated #1885]
  -> dense generator / nonnegative OS Hamiltonian                   [Integrated #1886]
  -> self-adjoint graph-closed Hamiltonian / positive resolvent      [Integrated #1887-#1888]
  -> Yosida convergence / bounded exponential semigroups            [Integrated #1889-#1893]
  -> exact generator = negative closed Hamiltonian                  [Integrated #1894]
  -> same-root vacuum / Ω⊥ excitation sector                        [Integrated #1895]
  -> ‖Ω‖=1, exact centering, excitation semigroup package           [Integrated #1896]
  -> ∃ m > 0, H̄|Ω⊥ >= m                                           [OPEN NOW]
  -> same-root exponential excitation decay                         [OPEN downstream]
  -> same-root positive spectral gap above Ω                        [OPEN downstream]

OLDER GENERIC PHYSICAL OS / HAMILTONIAN LANE

physical OS correlation calculus                                   [Integrated infrastructure]
  -> physical OS infrared mass                                      [Integrated infrastructure]
  -> graph-closed physical Hamiltonian variational mass             [Integrated infrastructure]
  -> Mathlib Gronwall / full-sector decay                           [Integrated infrastructure]
  -> physicalYangMillsOSInfraredMass = physicalYangMillsMass        [Integrated infrastructure]
  -> physical mass = greatest uniform decay rate                    [Integrated infrastructure]
  -> exact carrier/model bridge to newer same-root scalar Hilbert   [OPEN]

FULL 4D YANG--MILLS LANE

primary scalar rational-time process                               [Integrated]
  -> sufficiently rich interacting continuum gauge-field/state      [OPEN]
  -> full Euclidean/gauge/regularity/clustering package             [OPEN]
  -> nontrivial physical excitation theory from the same root        [OPEN]
  -> final positive mass-gap theorem                                [OPEN]

SIGNED-SPATIAL / GLUEBALL-GEOMETRY LANE

48-element signed spatial vertex action                            [Integrated]
  -> signed edge / boundary-step action                             [Integrated]
  -> actual gauge-configuration action + composition                [Integrated #1876]
  -> plaquette-holonomy covariance                                  [OPEN]
  -> cubic irrep / continuum-spin identification                    [OPEN]
  -> glueball spectral statements                                   [OPEN]

FINITE-TO-CONTINUUM RATE LANE

intrinsic finite Wilson rate + canonical slow states               [Integrated machinery]
  -> selected moving-time o(a_n) residual                           [OPEN]
  -> intrinsic finite Wilson rate = same-root/physical mass         [Conditional route]

EXACT-VALUE LANE

actual model-derived component extrema + sharpness                 [OPEN]
  -> independent physical normalization                             [OPEN]
  -> physical interpretation of normalized 33/20 endpoint           [OPEN]
```

---

# Phase 0 — Authority, replay, and claim discipline

**Status: Integrated and permanent.**

Repository rules:

```text
start ordinary PRs from the exact authoritative SHA
start ordinary proof PRs as Draft
use the GitHub connector as the canonical repository-operation path
judge CI only after workflow / job / Lean step are all completed
do not write to a PR head while CI is queued or in_progress
fix only after completed failure and after re-checking the exact head
keep development additive / tighten-only
never introduce sorry / admit / axiom / placeholder constants
fix the final head before Ready
re-check exact head / base / mergeability / reviews / threads before merge
integrate green PRs by normal merge with expected head pinned
record the actual merge SHA returned by the merge action
verify canonical is identical / ahead 0 / behind 0 after merge
start the next Draft from that exact SHA.
```

Claim discipline is part of the mathematics. In particular, no result may be moved between the newer same-root regular direct-limit carrier and the older abstract `PhysicalHilbert` carrier without an exact theorem-level bridge.

---

# Phase 1 — Actual finite compact `SU(N)` Wilson root

**Status: Integrated.**

The finite model contains the actual periodic-even compact `SU(N)` Wilson Gibbs probability law and its finite OS geometry.

Integrated surfaces include:

```text
periodic lattice / oriented edge / plaquette geometry
normalized Haar probability structure
Wilson action and Gibbs density
reflection geometry and boundary fiber decomposition
finite Wilson Gram-square / reflection-positivity theorem
gauge covariance of plaquette holonomies
normalized real trace-power gauge invariance
integer temporal covariance / finite reflection covariance.
```

Permanent boundary:

- the interacting boundary marginal is not replaced by Haar measure at nonzero coupling;
- finite Wilson OS positivity is theorem-generated, not assumed as a terminal positivity premise.

---

# Phase 2 — One-sided primary rational path and same-root scalar continuum law

**Status: Integrated.**

The earlier full boundary-vacuum readout contains both primary and antipodal reflection-fixed slices, so it is not treated as globally positive-half local.

The canonical route instead uses the primary fixed slice only:

```text
primary reflection-fixed spatial boundary carrier
  -> positive integer temporal readout
  -> theorem-generated negative-half independence on its valid reach
  -> finite bounded-measurable Wilson cylinder OS positivity
  -> reflection completion using the same finite Wilson source
  -> canonical primary plaquette scalarization
  -> fixed scalar path carrier ℚ -> ℝ.
```

The scalar coordinate is the canonical orientation-correct primary plaquette normalized trace / Wilson class function already constructed in the finite model.

The full reflected path is constructed without assuming a false global identity such as

```text
floor(-q / a) = -floor(q / a).
```

Negative rational times are supplied through actual source reflection.

---

# Phase 3 — Prokhorov continuum OS positivity and reflection invariance

**Status: Integrated.**

The scalar rational path carrier is a countable product Polish space. Tightness/Prokhorov machinery extracts a subsequential continuum probability law from the same finite Wilson pushforwards while preserving the physical scaling subsequence.

## PR #1802 — continuum rational-cylinder OS positivity

For every bounded-continuous cylinder on finitely many nonnegative rational times, the canonical same-root continuum law satisfies

```text
0 <= ∫ x, F(x) * F(Θ x) ∂ L.continuumMeasure,
Θ x q = x (-q).
```

The proof composes:

```text
actual finite Wilson positivity
+ primary temporal-reach geometry
+ exact finite scalar path readback
+ weak convergence of the same path laws
+ eventual finite-slot admissibility.
```

No continuum reflection-positivity premise is introduced.

## PR #1803 — intrinsic reflection invariance

The same continuum scalar law satisfies

```text
map Θ L.continuumMeasure = L.continuumMeasure.
```

## PR #1804 — fixed-slot OS bilinear forms

For every finite nonnegative rational slot sector `J`, the repository constructs a symmetric positive-semidefinite real bilinear form

```text
B_J(F,G) = E[(Θ F) G].
```

### Completion criterion — satisfied

This phase is complete because continuum OS positivity is available on the actual same-root primary scalar path law. The old roadmap's statement that this was the immediate blocker is obsolete.

---

# Phase 4 — Fixed-slot OS quotient, Hilbert completion, and directed system

**Status: Integrated.**

For each finite nonnegative rational slot sector, the repository constructs

```text
OS seminormed cylinder carrier
  -> OS null quotient / separation quotient
  -> real Hilbert completion.
```

Canonical finite-slot inclusions are proved isometric and compatible. The fixed-slot Hilbert sectors therefore form a directed system.

The repository constructs:

```text
algebraic Hilbert direct limit
  -> canonical normed structure
  -> uniform completion / completed direct-limit Hilbert carrier.
```

Time translation is transported through the same fixed-slot/directed-limit structure rather than installed on a duplicate Hilbert carrier.

---

# Phase 5 — Same-root OS contraction and rational semigroup

**Status: Integrated.**

The key finite-slot midpoint identity gives

```text
‖T_t F‖² <= ‖F‖ * ‖T_(2t) F‖.
```

A separate shift-independent bound gives

```text
‖T_s F‖ <= ‖F.observable‖∞.
```

PR #1845 combines those facts by dyadic iteration and proves the genuine same-root contraction

```text
‖T_t F‖ <= ‖F‖
```

for every nonnegative rational `t`.

The contraction is then lifted through separation quotient, fixed-slot Hilbert completion, algebraic direct limit, and completed direct limit.

PR #1883 closes exact rational semigroup coherence on the completed direct limit:

```text
T_0 = I,
T_s (T_t x) = T_(s+t) x.
```

Permanent boundary:

> Rational semigroup laws plus contractivity do not imply strong continuity at zero.

The repository therefore does not postulate continuity on the entire completed direct-limit carrier.

---

# Phase 6 — Canonical regular sector and real `C₀` OS semigroup

**Status: Integrated.**

## PR #1884 — regular real-time OS package

The canonical zero-time regular sector consists of vectors whose actual rational OS orbit converges strongly back to the initial vector as rational time tends to zero from the right.

The package proves:

```text
linearity and rational-time invariance of the regular sector
right continuity at every rational time
uniform continuity of every regular rational orbit
canonical dense extension NNRat -> NNReal
real-time contractivity
real-time OS symmetry and positivity.
```

## PR #1885 — endomorphism-valued real semigroup

Real-time values are proved to remain inside the regular sector and the exact additive law is closed there.

The result is a genuine strongly continuous contraction semigroup

```text
T : NNReal -> ContinuousLinearMap H_reg H_reg
```

with

```text
T_0 = I,
T_s T_t = T_(s+t),
‖T_t x‖ <= ‖x‖,
T_t x -> x as t -> 0+.
```

### Completion criterion — satisfied

The same-root primary scalar OS reconstruction now has an actual real-time `C₀` contraction semigroup on a complete Hilbert carrier.

---

# Phase 7 — Generator, graph-closed Hamiltonian, resolvent, and self-adjointness

**Status: Integrated.**

## PR #1886 — generator package

The right-generator domain is defined from actual strong difference quotients of the real same-root semigroup.

```text
A_OS = right generator,
H_OS = -A_OS.
```

The domain is dense. The generator/Hamiltonian is symmetric in the appropriate sense, `A_OS` is dissipative, `H_OS` has nonnegative quadratic form, and both are sequentially closable.

## PR #1887 — graph closure and self-adjoint Hamiltonian

The graph-closed Hamiltonian `H̄` is constructed as a Mathlib `LinearPMap` and shown to be self-adjoint using the same-root semigroup and positive-shift range theorem.

Integrated consequences include:

```text
dense closed domain
formal symmetry
quadratic-form nonnegativity
positive-shift lower bounds
closed range
finite Laplace vector resolvent identity
surjectivity / bijectivity of λ I + H̄ for λ > 0
H̄ = H̄†.
```

## PR #1888 — positive resolvent and Yosida contraction

For `λ > 0`, define

```text
R_λ = (λ I + H̄)⁻¹,
J_λ = λ R_λ.
```

The repository proves

```text
‖R_λ x‖ <= λ⁻¹ ‖x‖,
‖R_λ‖ <= λ⁻¹,
‖J_λ x‖ <= ‖x‖,
‖J_λ‖ <= 1,
```

and the standard resolvent identity.

---

# Phase 8 — Yosida approximation and exact generator/Hamiltonian identification

**Status: Integrated.**

PRs #1889-#1893 close the standard Yosida approximation route on the same carrier.

Integrated chain:

```text
J_(2^n) x -> x on dom(H̄)
  -> J_(2^n) x -> x on the full regular Hilbert carrier
  -> H_(2^n) x -> H̄ x on dom(H̄)
  -> bounded exponential semigroups E_n(t) = exp(-t H_(2^n))
  -> contraction of E_n(t)
  -> locally uniform convergence on compact time intervals
  -> E_n(t) x -> T_t x for every regular vector.
```

This identifies the original OS semigroup as the strong Yosida exponential limit without assuming `T_t = exp(-tH̄)` from a spectral functional calculus.

## PR #1894 — exact domain/operator identity

The infinite Laplace-resolvent argument proves the reverse generator-domain inclusion and closes

```text
D(A_OS) = D(H̄),
A_OS = -H̄,
H_OS = H̄.
```

### Completion criterion — satisfied

The graph-closed self-adjoint Hamiltonian is now exactly the infinitesimal Hamiltonian of the original same-root regular OS `C₀` semigroup.

---

# Phase 9 — Normalized vacuum and exact excitation carrier

**Status: Integrated.**

## PR #1895 — same-root vacuum and `Ω⊥`

The vacuum is constructed from the literal constant-one cylinder in the empty finite rational slot sector.

Theorems include

```text
T_t Ω = Ω,
Ω ∈ D(A_OS),
A_OS Ω = 0,
Ω ∈ D(H̄),
H̄ Ω = 0.
```

Define

```text
Ω⊥ = {x | inner ℝ Ω x = 0}.
```

The repository proves:

```text
Ω⊥ is complete;
T_t preserves Ω⊥;
H̄ preserves Ω⊥ on its exact closed-domain intersection;
the exact restricted graph-closed Hamiltonian is formally symmetric.
```

## PR #1896 — normalization and centering

The constant-one OS state is evaluated directly against the continuum probability law and transported through the full same-root reconstruction:

```text
‖Ω‖ = 1,
inner ℝ Ω Ω = 1,
Ω != 0.
```

Define

```text
c_Ω(x) = inner ℝ Ω x,
x° = x - c_Ω(x) • Ω.
```

The repository proves

```text
x° ∈ Ω⊥,
c_Ω(x) • Ω + x° = x,
centering fixes already-orthogonal vectors,
c_Ω(T_t x) = c_Ω(x),
T_t(x°) = (T_t x)°.
```

The semigroup is corestricted to the complete excitation carrier with exact zero-time, additive, and contraction laws.

The exact same-root coercivity predicate is also exposed on the vacuum-orthogonal closed Hamiltonian domain.

---

# Phase 10 — Strictly positive same-root excitation coercivity

**Status: OPEN NOW — immediate principal frontier.**

The target is to prove the existence of a positive constant on the exact carrier already constructed:

```text
∃ m : ℝ,
  0 < m ∧
  FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt P m.
```

Equivalently, for every exact excitation-domain vector,

```text
m * ‖x‖^2 <= inner ℝ x (H̄ x).
```

This must be a theorem of the same Wilson / primary-scalar / Prokhorov root.

## Preferred constructive route

The next proof package should search for the strongest already-integrated quantitative statement that can be transported without changing carriers. Preferred order:

```text
1. identify an actual finite-Wilson or same-root scalar quantitative lower-bound certificate;
2. express it on the canonical primary-scalar OS cylinder/Hilbert objects;
3. prove uniformity strong enough to survive the selected continuum limit;
4. pass the estimate through the fixed-slot / direct-limit construction;
5. extend from the canonical dense/core domain to the exact graph-closed excitation domain;
6. conclude strict positivity of the already-defined same-root coercivity predicate.
```

If an existing older physical coercivity theorem is considered, an exact same-carrier bridge must be proved first. Matching theorem names, analogous formulas, or a shared informal interpretation are not sufficient.

## Anti-shortcuts

Do not:

```text
insert m > 0 as a fresh physical assumption
identify the older PhysicalHilbert with the newer same-root Hilbert by notation
infer full-sector coercivity from one scalar cyclic correlation without density/cyclicity closure
transfer a numerical mass from the conditional exact-value lane
infer a positive gap solely from contractivity, self-adjointness, or H̄ Ω = 0.
```

## Completion criterion

Phase 10 is complete only when the authoritative same-root carrier contains a theorem with an explicit existential positive lower bound, not merely the definition of the coercivity predicate.

---

# Phase 11 — Same-root decay and spectral-gap consequences

**Status: OPEN downstream.**

Once Phase 10 supplies `m > 0`, derive the consequences on the same carrier.

Target semigroup statement:

```text
forall t : NNReal,
forall x : Ω⊥,
  ‖T_t x‖ <= exp (-m * t) * ‖x‖
```

or the exact equivalent form supported by the repository's real conventions.

Target Hamiltonian/spectral statement:

```text
vacuum eigenvalue = 0
and
spectrum(H̄ on Ω⊥) ⊆ [m, ∞).
```

The full closed Hamiltonian is already self-adjoint and the vacuum/excitation decomposition is canonical. Any remaining restricted-self-adjointness or reducing-subspace lemmas needed for a clean spectral statement should be proved additively from that structure.

### Completion criterion

A same-root mass-gap theorem must be stated on the newer regular direct-limit carrier itself, with no hidden transfer from the older generic physical carrier.

---

# Phase 12 — Relation to the older generic physical OS / mass lane

**Status: Integrated infrastructure; exact bridge open.**

The older generic physical lane proves, under its explicit physical OS hypotheses,

```text
physicalYangMillsOSInfraredMass = physicalYangMillsMass
```

and identifies that mass with the greatest full vacuum-orthogonal uniform exponential semigroup decay rate.

The proof uses

```text
closed-Hamiltonian Rayleigh lower bound
  -> generator-domain orbit differential inequality
  -> real right-neighborhood slope control
  -> Mathlib scalar Gronwall
  -> generator-domain exponential decay
  -> density/closure to all vacuum-orthogonal states.
```

This machinery remains valuable, but the current same-root scalar Hilbert construction is not yet identified with the older abstract `PhysicalHilbert` carrier.

Two safe options are allowed:

```text
A. prove the needed decay/gap consequences directly on the same-root carrier; or
B. construct an exact linear-isometric/unitary/shared-carrier bridge and transport the generic theorem honestly.
```

Do not silently choose option B by definitional resemblance.

---

# Phase 13 — Extend from the primary scalar process to full 4D interacting Yang--Mills

**Status: OPEN.**

The current same-root continuum object is a real scalar rational-time process derived from the canonical primary plaquette normalized trace. It is not yet the complete continuum gauge field/state.

A Clay-level existence theorem still requires a sufficiently rich continuum construction carrying the needed local four-dimensional gauge-invariant observable content.

Required model-derived package includes, in the chosen rigorous formulation:

```text
four-dimensional Euclidean covariance
gauge covariance / gauge-invariant observable algebra
reflection positivity
regularity / temperedness or the selected formal substitute
clustering / vacuum uniqueness structure
finite-Wilson compatibility / continuum scaling relation
nontriviality
and the physical Hamiltonian realization.
```

The construction must remain anchored to the actual finite Wilson root rather than introducing an independent continuum theory by assumption.

### Important distinction

A positive gap proved first on the primary scalar OS Hilbert carrier would be a major same-root result, but it would still not by itself prove that the complete four-dimensional Yang--Mills physical Hilbert space has the same full-sector gap. The required richness/cyclicity/completeness bridge must be explicit.

---

# Phase 14 — Signed spatial symmetry and glueball geometry

**Status: Partially integrated.**

The finite-lattice signed-spatial lane now contains the abstract 48-element signed permutation action on the actual gauge-configuration carrier.

Integrated through PR #1876:

```text
signed spatial vertex action
  -> unit-step covariance
  -> signed boundary-step transport
  -> generic configuration pullback
  -> exact readback of swap12 / swap23 / axis-1 reflection
  -> exact composition law / monoid homomorphism into configuration permutations.
```

Open next steps:

```text
1. transport oriented plaquette holonomy under the full signed action;
2. prove covariance/invariance of the selected scalar plaquette observables;
3. construct cubic-group projection operators or equivalent representation data;
4. identify lattice cubic irreps of candidate gauge-invariant states;
5. only with a justified continuum limit discuss continuum spin;
6. only after spectral identification make glueball-mass statements.
```

No continuum glueball claim follows from finite cubic symmetry alone.

---

# Phase 15 — Selected moving-time finite-Wilson recovery

**Status: OPEN quantitative lane; generic machinery integrated.**

The repository retains intrinsic finite Wilson transfer rates and theorem-generated slow states.

The characteristic missing quantitative statement remains a selected moving-time residual of the form

```text
‖ iota_n(K_n^2 phi_n) - T(2 a_n) iota_n(phi_n) ‖
  <= 2 a_n delta_n,

delta_n -> 0.
```

Equivalently, the residual must be `o(a_n)`.

Ordinary fixed-time convergence is not a substitute because the relevant time itself shrinks with `a_n`.

A future identification of the intrinsic finite Wilson rate with a continuum mass requires both this quantitative closure and an exact common physical realization.

---

# Phase 16 — Exact-value and physical normalization lane

**Status: Conditional route; physical interpretation open.**

The repository contains structural exact-value assembly machinery and retains the normalized endpoint

```text
33/20.
```

A physical interpretation requires independent proofs of

```text
actual model-derived component decomposition
actual component Rayleigh extrema
required sharpness / attainment
identification with the relevant same-root/full physical mass
physical reference-time / unit normalization.
```

No coefficient may be assigned merely to manufacture the target rational number.

Permanent distinctions:

```text
finite Z₂ geometric cap / coercivity 1/2
  != intrinsic compact-Wilson finite rate
  != any future same-root primary-scalar coercive mass
  != older generic physicalYangMillsMass unless bridged
  != normalized conditional endpoint 33/20.
```

---

# Immediate next proof package

From canonical exact SHA

```text
777e48e54b1bdb8028d624513568be476a415e1d
```

the safest additive mathematical order is now:

```text
1. inspect the exact same-root excitation Hamiltonian/coercivity interfaces introduced in #1895-#1896;
2. identify the strongest existing actual-Wilson or primary-scalar quantitative estimate that can feed them without changing carrier;
3. prove any missing dense-core / closed-domain transport lemmas;
4. derive an explicit theorem ∃ m > 0 with same-root excitation coercivity;
5. derive same-root excitation-semigroup exponential decay;
6. close the corresponding spectral lower bound above the normalized vacuum;
7. only then decide whether an exact bridge to the older generic PhysicalHilbert lane adds mathematical value;
8. continue the independent full-4D gauge-field and signed-spatial/glueball geometry lanes without conflating their carriers.
```

The preferred proof style remains:

```text
reuse Mathlib
reuse existing actual Wilson geometry
stay on the same constructed root whenever possible
prove exact carrier bridges when transport is necessary
avoid generic wrapper proliferation
avoid strengthening assumptions merely to activate a theorem.
```

---

# Anti-goals

Do not:

- claim the Clay Millennium problem is solved before the full model-facing construction is complete;
- describe same-root continuum OS positivity as still open — it is integrated for the primary scalar rational-time process;
- describe the primary scalar process as the complete continuum gauge connection;
- infer a positive gap merely from self-adjointness, contractivity, or the existence of a normalized vacuum;
- infer whole-excitation-sector coercivity from one nonzero scalar state without the needed density/cyclicity argument;
- identify the newer same-root regular direct-limit Hilbert carrier with the older generic `PhysicalHilbert` without an exact bridge;
- transport `physicalYangMillsMass`, `1/2`, or `33/20` onto the newer same-root carrier without a theorem;
- identify the finite signed spatial action with a continuum glueball spin classification without plaquette/representation/continuum bridges;
- replace the selected moving-time `o(a_n)` condition by fixed-time convergence;
- add `sorry`, `admit`, `axiom`, or placeholder constants.

---

# Completion criterion for the program

The full program is complete only when a single explicit theorem chain begins from an actual interacting four-dimensional compact-gauge Yang--Mills construction and reaches a reconstructed physical Hilbert theory with a normalized vacuum and a strictly positive non-vacuum spectral lower bound for the physical Hamiltonian, with the required continuum OS, gauge, Euclidean, regularity, clustering/nontriviality, finite-Wilson compatibility, and normalization inputs constructed rather than merely supplied.

The current canonical result is an important but narrower milestone: the same actual Wilson root now reaches a genuine primary-scalar continuum OS Hilbert reconstruction, real `C₀` semigroup, self-adjoint graph-closed Hamiltonian, normalized vacuum, and exact vacuum-orthogonal excitation carrier. The next missing mass-gap datum is **strictly positive same-root excitation coercivity**.
