# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-09 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest merged canonical checkpoint at the start of this documentation refresh is

```text
97945a33d872de268b8f0cd14831f40fb12d733f
```

which is the normal merge of PR #3704,

```text
Reduce six-spatial ground-state frame to mean-projection contraction.
```

The active validated mathematical unit is PR #3707,

```text
Route twelve-spatial joint Poincare to the physical transfer gap.
```

Its exact Lean proof head before this docs-only refresh is

```text
eb8ae2b7e4c07fe266810076a416d4da80f3122a
```

with PR Lean Fast Check #13406 completed / success, including the `Run changed Lean fast check` step.

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status. A green open PR is a validated candidate unit, not yet canonical mathematics.

> **Current frontier**
>
> The fixed-finite-volume physical-pair program is mature: decomposition, strict contraction, power decay, strong convergence, fixed-space characterization, coercivity, real spectral confinement, resolvent estimates, Green operator, exact reduced range, and a relative Poincaré estimate are already integrated.
>
> The active mass-gap route has now been pushed upstream into the **actual ground-state Wilson joint law**. Six genuine right spatial conditional expectations and six genuine left spatial conditional expectations have been constructed on one joint `L²` carrier. The concrete physical eight-color defect has been reduced to the six genuine spatial residuals, and the six-spatial frame problem has been reduced exactly to a mean-projection contraction theorem.
>
> PR #3707 further proves, at its green proof head, that the conventional twelve-color residual is one half of the six-spatial residual on right-boundary lifts. Consequently a twelve-color Poincaré coefficient `κ` yields the physical transfer-gap lower bound `3κ/4`.
>
> The immediate genuine analytic/geometric problem is therefore to prove the **common-fixed-space identification and a positive scale-independent `L²` Poincaré coefficient for the actual twelve-spatial ground-state conditional-expectation dynamics**, using Wilson / Doob / Harnack structure rather than a new abstract hypothesis.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Green candidate** — exact Lean proof is green on an open PR but not yet merged.
- **Integrated implication machinery** — theorem chain is formalized, but a model-facing input remains.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Diagnostic only** — correct theorem/obstruction that is not the active gap mechanism.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                         [Integrated]
  -> reflection positivity / boundary geometry                       [Integrated]
  -> physical spatial-slice transfer                                 [Integrated]
  -> positive / ground-state transfer geometry                       [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> rational/continuum scalar law                                   [Integrated]
  -> continuum OS positivity                                         [Integrated]
  -> direct-limit Hilbert carrier                                    [Integrated]
  -> real C₀ semigroup                                               [Integrated]
  -> graph-closed self-adjoint Hamiltonian                           [Integrated]
  -> vacuum Ω / complete Ω⊥                                          [Integrated]

C. FINITE PHYSICAL-PAIR THEORY

one-slice F ⊕ Fᗮ                                                    [Integrated]
  -> completed TT / NN decomposition inside PP                       [Integrated]
  -> q = ‖R‖ < 1                                                     [Integrated]
  -> q^k decay / strong convergence to P_TT                           [Integrated]
  -> Fix(S₂|PP)=TT                                                   [Integrated]
  -> coercivity / spectrum / resolvent / Green                       [Integrated]
  -> exact reduced range / relative Poincaré                          [Integrated]

D. GROUND-STATE WILSON JOINT-LAW GEOMETRY

one-slab ground-state joint probability law                          [Integrated]
  -> left/right boundary L² isometries                               [Integrated]
  -> Doob/coarse conditional-expectation geometry                     [Integrated]
  -> 6 right spatial condExp projections                             [Integrated]
  -> 6 left spatial condExp projections                              [Integrated]
  -> genuine two-sided 12-spatial family                             [Integrated]
  -> qualitative common-fixed iff right-six fixed and left-six fixed [Integrated]

E. CONCRETE PHYSICAL DEFECT ROUTE

6 spatial + 2 temporal identities = concrete 8-color family          [Integrated]
  -> 8-color residual = 3/4 * 6-spatial residual                     [Integrated]
  -> η=1 residual-to-raw-physical-defect comparison                  [Integrated]
  -> six-spatial frame κ -> physical gap >= 3κ/8                     [Integrated]

F. SIX-SPATIAL DIRICHLET / CONTRACTION REDUCTION

E₆(u) = ‖u‖² - (1/6)Σ_c ‖P_c R u‖²                                 [Integrated: #3704]
  -> frame κ <-> mean-projection contraction 1-κ                     [Integrated]
  -> q<1 -> physical transfer gap >= 3(1-q)/8                        [Integrated]

G. TWELVE-SPATIAL POINCARE ROUTING

E₁₂(z) = 1/2(E₆,right(z)+E₆,left(z))                                [Green candidate: #3707]
  -> on right lift E₁₂(Ru)=1/2 E₆(u)                                [Green candidate]
  -> 12-color Poincaré κ -> six-spatial frame 2κ                     [Green candidate]
  -> physical transfer gap >= 3κ/4                                  [Green candidate]

H. PRESENT MODEL-FACING FRONTIER

identify actual 12-color common-fixed space                          [OPEN NOW]
  + prove global L² Poincaré/coercivity for the 12-block dynamics    [OPEN NOW]
  + make κ scale-independent along the physical family               [OPEN NOW]
  using Wilson / Doob / Harnack conditional-law structure            [OPEN NOW]
  -> scale-uniform physical transfer gap                             [OPEN DOWNSTREAM]

I. CONTINUUM / THERMODYNAMIC PROPAGATION

uniform finite-volume physical transfer gap                          [OPEN DOWNSTREAM]
  -> stable Green/Poincaré/resolvent control                         [OPEN DOWNSTREAM]
  -> thermodynamic/scaling-limit physical carrier                    [OPEN DOWNSTREAM]
  -> OS/Wightman spectral lower bound on actual physical sector      [OPEN DOWNSTREAM]

J. SU(2) EXACT-MODE LANE

selected physical/top endpoint pair                                 [Integrated]
  -> literal raw one-slab kernel coefficient                         [Integrated]
  -> realizable raw one-step limit/coherence                         [OPEN NOW, parallel]
  -> selected completed-boundary weak identity                       [generated downstream]
  -> exact common-carrier mode                                       [Integrated implication machinery]
  -> Ω⊥ Hamiltonian mode at exactGapValueReal                        [Integrated implication machinery]

K. CLAY-LEVEL COMPLETION

full same-root 4D continuum gauge field/state                        [OPEN]
correct vacuum structure                                             [OPEN]
full physical OS/Wightman identification                             [OPEN]
strict positive spectrum above vacuum                                [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
use GitHub-mediated repository operations
accept CI only when workflow/job/Lean step are terminal success
never treat queued or in_progress as success
write-freeze while exact-head CI is running
inspect terminal failure logs before editing
keep proof development additive/tighten-only
forbid proof placeholders in theorem source
fresh-check exact head/base/mergeability/reviews/threads before merge
normal-merge with expected head SHA fixed
verify merge parents and canonical branch pointer
verify post-merge canonical CI and trusted cache
```

Claim discipline:

```text
finite theorem != continuum theorem
q_n < 1 for every n != inf_n(1-q_n)>0
local conditional-law comparison != global L² Poincaré theorem
qualitative common-fixed characterization != quantitative spectral gap
relative top block != unique vacuum line
one positive exact mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
green open PR != merged canonical theorem status
```

Current authoritative CI uses Lean `4.30.0-rc2` and Lake `5.0.0-src+3dc1a08` at this checkpoint.

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the actual periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include:

```text
oriented lattice / edge / plaquette geometry
normalized Haar probability structure
Wilson action / Gibbs density / probability measure
reflection-fixed geometry and positive-time decomposition
finite Wilson reflection positivity
boundary and spatial-slice coordinate systems
gauge-covariant holonomy
gauge-invariant normalized trace observables
integer temporal translation / reflection covariance
finite support geometry
one-slab Wilson kernels and transfer operators
```

### Permanent rule

Keep the interacting Wilson model visible through every decisive physical bridge. Do not replace it by a product measure or abstract projection family unless an explicit theorem justifies the replacement.

---

# Phase 2 — Same-root primary scalar continuum law

**Status: Integrated.**

Integrated route:

```text
finite primary gauge-invariant scalar readout
  -> reflection-completed rational-time path
  -> scalar path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
```

This is a same-root continuum observable process, not yet the complete gauge field on `ℝ⁴`.

---

# Phase 3 — Continuum OS Hilbert reconstruction and Hamiltonian

**Status: Integrated.**

Integrated chain:

```text
continuum rational-cylinder OS positivity
continuum reflection invariance
OS null quotient
fixed-slot real Hilbert completions
isometric directed system
completed direct-limit carrier
NNReal strongly continuous contraction semigroup
right generator / right Hamiltonian
graph closure as a mathlib linear partial operator
self-adjoint graph-closed Hamiltonian
resolvent / Yosida recovery
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This phase is not the immediate blocker.

---

# Phase 4 — Transfer spectral / logarithmic-generator / Wightman lane

**Status: Integrated analytic machinery; model realization remains relevant.**

Canonical machinery includes:

```text
positive compact transfer spectral support
strictly-positive transfer support
partially-defined logarithmic generator
resolvent/effective-energy identities
intrinsic logarithmic spectral floor
spectral-mode eigenvector/domain theorems
canonical spectral span as an operator core
common-core Hilbert equivalence machinery
self-adjoint maximality / closure transfer
transfer point-energy <-> target Hamiltonian point-energy implications
attained mass-gap certificate implications
```

The abstract operator theory is not the present bottleneck. The key issue is model-derived uniform coercivity on the actual physical carrier.

---

# Phase 5 — Completed finite-volume physical-pair geometry and dynamics

**Status: Integrated.**

Let

```text
F  = full eigenvalue-one subspace of normalized one-slice physical transfer
K  = Fᗮ
PP = completed physical pair carrier
TT = completed top-top block
NN = completed non-top block inside PP
R  = one-slice orthogonal transfer restriction
q  = ‖R‖
S₂ = normalized physical pair transfer
SN = restriction of S₂ to NN
```

The integrated chain proves:

```text
TT ⟂ NN
PP = TT ⊕ NN
NN = PP ⊓ TTᗮ
q < 1
‖SN‖ ≤ q
‖SN^k x‖ ≤ q^k ‖x‖
S₂^k x -> P_TT x
Fix(S₂|PP)=TT
(1-q)‖x‖ ≤ ‖x-SN x‖
spectrum ℝ SN ⊆ [-q,q]
real resolvent bound outside [-q,q]
G=(I-SN)⁻¹ with ‖G‖≤(1-q)⁻¹
range(I-S₂|PP)=NN
relative Poincaré estimate on PP
```

### Current role

This theory is now downstream infrastructure. It shows what follows from finite-volume separation, but the active proof program seeks a stronger model-facing quantitative source of separation in the actual ground-state Wilson dynamics.

---

# Phase 6 — Physical ground state, joint law, and Doob geometry

**Status: Integrated.**

The repository has constructed the actual physical ground-state route needed to avoid an abstract color-projection seam.

Integrated objects and theorems include:

```text
positive / strictly-positive top eigenvector structure
ground-state normalized one-slab law
genuine left/right joint probability measure
left-boundary L² isometry
right-boundary L² isometry
coarse conditional expectation
Doob boundary operator
Wilson marginal / conditional-measure comparison
continuous-vacuum normalization
```

### Carrier rule

The ground-state joint `L²` carrier is not silently identified with the independent global Gibbs `L²` carrier. Any bridge between them must be explicit.

---

# Phase 7 — Genuine right six and left six spatial conditional expectations

**Status: Integrated.**

For each spatial color, the right-side update is a genuine `condExpL2` projection retaining the opposite boundary plus the off-color right data. The left-side construction is its exact counterpart.

Integrated facts:

```text
6 genuine right spatial conditional expectations
6 genuine left spatial conditional expectations
idempotence of every projection
Hilbert symmetry of every projection
explicit two-sided color type Sum (Fin 6) (Fin 6)
12-color family on one joint L² carrier
cardinality = 12
common fixed by all 12
  <-> fixed by all right 6 and all left 6
all left 6 fix every right-boundary lift
```

### What is not yet integrated

The qualitative fixed-space equivalence is not yet a theorem identifying the common-fixed sector with the precise physical vacuum/coarse sector needed for a global Poincaré theorem.

That identification is part of the immediate frontier.

---

# Phase 8 — Concrete eight-color residual to raw physical defect

**Status: Integrated.**

The model-facing eight-color family is now

```text
6 genuine ground-state spatial condExp projections
+ 2 identity temporal slots.
```

The temporal slots contribute zero residual, so the eight-color residual is exactly the six-spatial residual with the normalization factor inherited from `1/8` rather than `1/6`.

The canonical theorem route gives, at `η=1`,

```text
actual ground-state color residual
  -> raw physical one-slab squared defect.
```

Combining this with the top-orthogonal transfer-gap bridge removes the old independent abstract comparison hypothesis from the final model-facing route.

---

# Phase 9 — Six-spatial frame reduction

**Status: Integrated.**

The concrete eight-color route is reduced to the actual six-spatial residual

```text
E₆(u) = (1/6) Σ_{c:Fin 6} ‖R u - P_c R u‖².
```

A six-spatial frame coefficient `κ` gives the physical top-eigenspace transfer-gap bound

```text
physical transfer gap >= 3κ/8.
```

This factor is the exact consequence of the `1/8` physical color normalization versus the six active spatial slots.

---

# Phase 10 — Mean-projection formulation of the six-spatial problem

**Status: Integrated through PR #3704.**

For the six genuine orthogonal projections,

```text
E₆(u)
  = ‖u‖² - (1/6) Σ_c ‖P_c R u‖².
```

Therefore

```text
κ ‖u‖² ≤ E₆(u)
```

is equivalent to

```text
(1/6) Σ_c ‖P_c R u‖² ≤ (1-κ) ‖u‖².
```

For a contraction coefficient `q≤1`,

```text
mean projected norm² ≤ q ‖u‖²
```

gives

```text
physical transfer gap >= 3(1-q)/8.
```

For `q<1`, the finite-volume gap is positive.

### Meaning

The unresolved frame theorem has been converted into a concrete spectral/contraction question for the actual six ground-state conditional expectations.

---

# Phase 11 — Twelve-spatial normalization and physical routing

**Status: Green candidate in PR #3707.**

Define the conventional twelve-spatial residual on the joint carrier by

```text
E₁₂(z) = (1/12) Σ_{c:12 colors} ‖z-P_c z‖².
```

The green proof unit establishes

```text
E₁₂(z)=1/2(E₆,right(z)+E₆,left(z)).
```

Since every left projection fixes every right-boundary lift,

```text
E₁₂(Ru)=1/2 E₆(u).
```

Hence

```text
κ ‖x‖² ≤ E₁₂(RUx)
```

implies

```text
2κ ‖x‖² ≤ E₆(Ux)
```

and therefore

```text
physical transfer gap >= 3κ/4.
```

The condition `κ≤1/2` only keeps the induced six-spatial frame coefficient `2κ` inside the normalized interval; an arbitrary positive coefficient can be reduced if necessary.

### Merge criterion

Before this phase becomes canonical:

```text
exact PR head/base fresh
PR open / merged=false / mergeable=true
exact-head CI terminal success
reviews and inline threads checked
normal merge with expected head
merge parents verified
post-merge canonical CI terminal success
```

---

# Phase 12 — Identify the actual twelve-color common-fixed space

**Status: OPEN NOW — highest-priority geometric frontier.**

The repository already proves

```text
fixed by all 12
  <-> fixed by right 6 and fixed by left 6.
```

The next theorem must identify the intersection of the retained sigma-algebras / projection ranges on the **actual ground-state joint law**.

The target should be stated at the strongest level that is really justified by the Wilson geometry. Candidate forms include identification with:

```text
the genuinely coarse joint sigma-algebra;
a boundary-vacuum-generated common sector; or
the exact common-fixed subspace needed to exclude physical top-orthogonal right lifts.
```

Do not assert “the common fixed space is constants” unless the sigma-algebra and measure-theoretic proof really establishes it.

### Completion criterion

Produce a theorem that lets a physical top-orthogonal right-boundary lift be placed in the orthogonal complement of the twelve-color common-fixed sector without adding an independent hypothesis.

---

# Phase 13 — Prove twelve-block `L²` Poincaré coercivity from Wilson / Doob / Harnack data

**Status: OPEN NOW — highest-priority analytic frontier.**

The repository already contains local conditional-law structure, including one-link Wilson/Doob/Harnack comparison and strict positivity information.

The desired global theorem is schematically

```text
κ ‖z‖² ≤ E₁₂(z)
```

on the orthogonal complement of the twelve-color common-fixed sector, with `κ>0` derived from the actual model.

A plausible proof architecture is:

```text
1. one-link conditional density / Doob comparison;
2. conditional variance lower bounds;
3. aggregate one-link variances into one spatial color block;
4. aggregate six right and six left blocks;
5. identify the common-fixed kernel of the resulting Dirichlet form;
6. establish a spectral/Poincaré lower bound on its orthogonal complement.
```

### Critical rule

Total-variation or Dobrushin influence control is not itself an `L²` Poincaré theorem. The passage must be formalized explicitly.

### Completion criterion

A theorem on the actual ground-state joint `L²` carrier supplies a positive `κ` with no abstract replacement projection family and no independent frame/comparison assumption.

---

# Phase 14 — Make the twelve-color coefficient scale-independent

**Status: OPEN NOW — coupled to Phase 13.**

A positive coefficient at each finite scale is not enough. For the physical scaling family we ultimately need

```text
∃ κ_* > 0, ∀ n,
  κ_* ‖x‖² ≤ E₁₂,n(R U x)
```

for the relevant physical top-orthogonal sector.

The coefficient must be derived from model quantities whose dependence on lattice size/coupling is controlled.

### Two acceptable outcomes

#### Route A — uniform twelve-block coercivity succeeds

Prove a model-derived `κ_*>0` and immediately obtain

```text
uniform physical transfer gap >= 3κ_*/4.
```

#### Route B — the candidate coefficient degenerates

Prove the degeneration honestly, identify which local-to-global estimate loses scale, and replace it by a stronger block, multiscale, or geometry-aware coercive quantity.

Do not hide degeneration behind a uniform assumption.

---

# Phase 15 — Uniform finite-volume consequences

**Status: OPEN DOWNSTREAM.**

Once a model-derived uniform physical transfer gap exists, specialize the already-integrated Hilbert/spectral machinery to obtain stable estimates such as

```text
uniform non-top contraction / decay as appropriate
uniform coercivity
uniform resolvent control
uniform Green bounds
uniform Poincaré estimates
stable reduced-range control
```

The exact form must respect the relevant physical carrier and top/common-fixed sector proved in Phases 12–14.

---

# Phase 16 — Thermodynamic and scaling-limit propagation

**Status: OPEN DOWNSTREAM.**

The next task is to propagate the uniform finite-volume information without losing same-root provenance.

Required ingredients may include:

```text
tightness / compactness for the relevant physical state family
compatibility of finite-volume Hilbert carriers
convergence of transfer / semigroup forms
Mosco/strong-resolvent/form convergence as appropriate
stability of the vacuum/common-fixed sector
passage of the positive lower spectral bound to the limit
```

No continuum gap is obtained merely by writing a uniform finite-volume inequality. The limiting operator and physical carrier must be constructed and identified.

---

# Phase 17 — Full same-root physical continuum carrier

**Status: OPEN DOWNSTREAM.**

The scalar continuum OS lane is already substantial, but a Clay-level theorem needs a sufficiently rich four-dimensional Yang--Mills field/state and its physical Hilbert reconstruction.

Required work includes some coherent version of:

```text
continuum gauge-invariant local observable algebra / distributions
Euclidean covariance
reflection positivity
regularity needed for OS reconstruction
nontriviality
physical Hilbert carrier
Hamiltonian and vacuum
connection to the finite Wilson approximants
```

The existing same-root scalar process is a building block, not the full endpoint.

---

# Phase 18 — SU(2) selected exact-mode lane

**Status: Integrated implication machinery; raw-model input remains open in parallel.**

The selected exact-mode route has been pushed upstream to

```text
selected physical/top endpoint pair
  -> literal one-slab Wilson Hilbert-Schmidt kernel coefficient
  -> projected synthesis approximation
  -> realizable integer one-step raw-kernel limit
  -> explicit finite/common-time coherence
  -> theorem-generated selected weak identity
  -> exact common-carrier mode
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal.
```

### Remaining seam

Prove the realizable raw one-step kernel limit and coherence directly from the finite Wilson model.

### Relationship to the global Poincaré route

```text
selected exact mode != global spectral floor
```

The exact-mode theorem may identify an attained positive energy, while the twelve-color program seeks control of the entire relevant orthogonal sector.

---

# Phase 19 — Vacuum/common-fixed structure

**Status: OPEN DOWNSTREAM.**

The finite physical-pair theory deliberately does not prove top-sector simplicity, and the twelve-color joint dynamics has its own common-fixed geometry.

Any final mass-gap theorem must state precisely which zero-energy/fixed sector is being quotiented out and prove the needed identification.

Potential requirements include:

```text
vacuum uniqueness or a correct replacement formulation
relation between finite top eigenspaces and continuum vacuum sector
relation between twelve-color common-fixed subspace and physical vacuum data
absence of hidden zero-energy sectors in the final carrier
```

Do not collapse these distinctions prematurely.

---

# Phase 20 — OS/Wightman physical spectral gap

**Status: OPEN DOWNSTREAM.**

After the full same-root physical continuum carrier and Hamiltonian are established, transfer the uniform coercivity into a theorem of the form

```text
spectrum(H_phys | Ω⊥) ⊆ [m,∞)
```

for some `m>0`, or the mathematically correct equivalent formulation if the vacuum sector is not one-dimensional.

This is where a finite-volume transfer-gap theorem becomes a continuum mass-gap theorem.

---

# Phase 21 — Clay-level completion

**Status: OPEN.**

A completed theorem must combine, on one coherent same-root construction,

```text
4D continuum Yang--Mills existence
Euclidean covariance
reflection positivity / OS axioms in the required form
regularity / distributional field structure
physical nontriviality
correct vacuum structure
Wightman/OS physical Hilbert realization
strictly positive spectral gap above the vacuum sector
```

Only after those obligations are actually discharged should the repository claim a complete Yang--Mills existence-and-mass-gap theorem.

---

# Diagnostic lane — high-temperature Dobrushin control

**Status: Diagnostic only for the continuum gap question.**

The repository contains explicit finite-volume Wilson/Dobrushin results. They are useful for checking local conditional-law dependence and for strong-coupling/high-temperature finite-volume analysis.

The simple coefficient based on

```text
(exp(4β)-1)/(exp(4β)+1)
```

approaches `1` as `β -> +∞`. Therefore a naive use of that coefficient alone cannot produce the required scale-independent continuum gap in the relevant large-`β` scaling regime.

This obstruction is informative: it motivates the present ground-state Doob / two-sided block-Poincaré route rather than invalidating it.

---

# Immediate execution order

The recommended next sequence is now:

```text
1. finish / merge the green twelve-spatial normalization bridge when the fresh merge gate is satisfied;
2. prove the twelve-color common-fixed-space identification on the genuine joint law;
3. derive a finite-volume twelve-block L² Poincaré theorem from Wilson/Doob/Harnack conditional variance;
4. tighten the coefficient to a scale-independent model-derived κ_* > 0;
5. invoke the existing exact route
     E₁₂ -> E₆ -> raw physical defect -> transfer gap
   to obtain gap >= 3κ_*/4;
6. propagate the uniform estimate through finite-volume Green/resolvent/Poincaré machinery;
7. prove thermodynamic/scaling-limit stability on the same-root physical carrier;
8. complete the continuum OS/Wightman spectral-gap theorem;
9. separately discharge the remaining full-field, vacuum, and exact-mode obligations needed for Clay-level completion.
```

This sequence avoids reintroducing abstract projection hypotheses and keeps the decisive analytic work attached to the actual Wilson ground-state probability law.

---

# Definition of success for the present milestone

The present ground-state block-dynamics milestone is complete only when Lean contains a theorem whose assumptions are model-derived and which provides a positive scale-independent coefficient for the actual twelve-color joint conditional-expectation Dirichlet form, sufficient to conclude a uniform positive physical transfer gap.

Schematically:

```text
actual Wilson / ground-state data
  -> common-fixed identification
  -> ∃κ_*>0 uniform twelve-color Poincaré
  -> six-spatial frame coefficient 2κ_*
  -> raw physical squared-defect coercivity
  -> physical transfer gap >= 3κ_*/4
```

Until that coefficient is proved from the model, the global mass-gap boundary remains open.