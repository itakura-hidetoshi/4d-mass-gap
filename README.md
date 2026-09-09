# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, ground-state conditional-expectation geometry, and the mass-gap problem.

The repository is organized around a strict separation between

1. what is proved for the actual finite periodic compact `SU(N)` Wilson model;
2. what is proved on same-root continuum / OS carriers constructed from Wilson observables;
3. what is proved for finite-volume physical transfer operators and their top-orthogonal sectors;
4. what is proved for the genuine Wilson ground-state joint law and its conditional expectations;
5. implication machinery whose quantitative model-facing hypothesis is still open; and
6. the remaining steps needed for a complete four-dimensional Yang--Mills existence-and-mass-gap theorem.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current canonical theorem branch has, however, moved past the former qualitative obstruction. The genuine two-sided twelve-spatial ground-state conditional-expectation family now has its common-fixed sector identified with constants, its zero-residual kernel identified with the intrinsic constant line in the actual joint `L²`, and its kernel proved trivial on the genuine physical full-top-orthogonal sector.
>
> The immediate open problem is therefore **quantitative**, not qualitative: prove a positive **scale-independent** Poincaré/coercivity coefficient for the actual twelve-spatial Wilson ground-state dynamics on the physical top-orthogonal right-boundary sector. The existing canonical implication then routes such a coefficient to a uniform positive physical transfer gap.

---

## Repository status — 2026-09-10 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Authoritative exact canonical SHA:
  f82275f25c7e33de1410ec1e58b3533097d9383b

Latest canonical theorem merge:
  PR #3775
  Close twelve-spatial kernel on physical top-orthogonal sector

Canonical merge-push validation:
  PR Lean Fast Check #13476 = completed / success

Public landing/docs branch:
  main

Lean:
  leanprover/lean4:v4.30.0-rc2

Mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6

Detailed development order:
  ROADMAP.md
```

Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status. The public `main` branch is a landing/documentation surface and must not be confused with the theorem carrier.

---

# The current proof picture

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> spatial-slice and boundary L² carriers
  -> normalized one-slab physical transfer
  -> positive / strictly-positive ground-state transfer structure

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C₀ contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. FINITE PHYSICAL TRANSFER / PAIR LANE

full normalized-transfer top eigenspace F
  -> K = Fᗮ
  -> completed physical pair carrier PP = TT ⊕ NN
  -> strict finite-volume non-top contraction
  -> power decay / strong convergence / resolvent / Green operator
  -> finite-volume relative Poincaré and spectral exclusion machinery

D. LOCAL WILSON / DOOB / HARNACK LANE

continuous positive physical vacuum
  -> one-link replacement geometry
  -> volume-independent local Harnack ratio exp(8 beta)
  -> Doob one-link conditional law
  -> centered one-link spectral gap = 1
  -> explicit local variance comparison factor exp(-16 beta)
  -> native Wilson conditional-variance / projection-defect bridge

E. GROUND-STATE JOINT-LAW TWELVE-SPATIAL LANE

actual ground-state one-slab joint probability law Π
  -> left/right boundary L² isometries
  -> 6 right genuine spatial condExp projections
  -> 6 left genuine spatial condExp projections
  -> one genuine two-sided 12-spatial family on joint L²
  -> right-six fixed => left-boundary measurable
  -> left-six fixed => right-boundary measurable
  -> pair-Haar two-boundary collapse
  -> common fixed by all 12 = ground-state-a.e. constants

F. RESIDUAL KERNEL LANE

E₁₂(z) = 0
  <-> z fixed by all 12
  <-> z is ground-state-a.e. constant                    [#3768]
  <-> z equals an actual constant vector in joint L²     [#3770]
  <-> z belongs to the intrinsic constant line           [#3773]

constant line ∩ constant lineᗮ = {0}                     [#3773]

physical x in full top-orthogonal sector K
  -> transformed/right-lifted vector lies in the relevant
     constant-line orthogonal geometry
  -> E₁₂(R U x) = 0  <->  x = 0                          [#3775]

G. CURRENT QUANTITATIVE FRONTIER

prove one scale-independent κ > 0 such that

  κ ||x||² <= E₁₂,n(R U x)

for every scale n and every physical x in K_n              [OPEN]

then the already-canonical routing gives

  12-spatial Poincaré κ
    -> six-spatial frame coefficient 2κ
    -> physical top-eigenspace transfer gap >= 3κ/4
    -> scale-uniform positive physical transfer gap

H. DOWNSTREAM CONTINUUM / CLAY COMPLETION

uniform finite-volume physical gap
  -> stable thermodynamic/scaling control                 [OPEN]
  -> actual physical continuum carrier / OS-Wightman link [OPEN]
  -> positive continuum spectrum above vacuum             [OPEN]
  -> full 4D Yang--Mills existence + mass gap             [OPEN]
```

The conceptual change is important:

```text
common-fixed identification                 DONE
qualitative residual-kernel identification DONE
physical top-orthogonal kernel triviality  DONE
positive uniform coercivity                 OPEN
```

A trivial kernel is **not** silently promoted to a quantitative or scale-uniform spectral gap.

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite model is built from the genuine compact gauge group

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law.

Canonical infrastructure includes

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and positive-time decomposition
finite Wilson reflection positivity / Gram identities
gauge covariance of plaquette holonomy
gauge invariance of normalized trace observables
integer temporal translation and reflection covariance
spatial-slice Haar-L² carriers
boundary Haar-L² carriers
one-slab Wilson kernels
normalized physical transfer operators
```

The interacting Wilson law is not replaced by product Haar at nonzero coupling unless an explicit theorem performs the required comparison or transport.

---

# 2. Same-root scalar continuum OS construction

The repository contains a constructive same-root scalar continuum OS lane obtained from actual finite Wilson pushforwards.

Integrated structure includes

```text
primary gauge-invariant scalar Wilson readout
reflection-completed rational-time paths
tightness / Prokhorov subsequential continuum law
continuum rational-cylinder reflection positivity
continuum reflection invariance
OS seminorm and null quotient
fixed-slot real Hilbert completions
directed-limit Hilbert carrier
real strongly continuous contraction semigroup
right generator and graph closure
self-adjoint graph-closed OS Hamiltonian
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This is a genuine same-root continuum observable process. It is **not** yet the complete four-dimensional continuum gauge field on `ℝ⁴`.

---

# 3. Finite-volume physical transfer and pair theory

At fixed finite-volume data, write schematically

```text
F   = full eigenvalue-one subspace of normalized physical transfer
K   = Fᗮ
PP  = completed physical pair carrier
TT  = completed top-top block
NN  = completed non-top block inside PP
R   = normalized one-slice restriction to K
q   = ||R||
S₂  = normalized physical pair transfer
```

The canonical branch contains, without assuming one-dimensionality of `F` or uniqueness of a vacuum vector,

```text
PP = TT ⊕ NN
NN = PP ⊓ TTᗮ
q < 1 at each fixed finite volume
non-top power decay
strong convergence to the top-top projection
fixed-space characterization
coercivity and real spectral confinement
resolvent estimates
non-top Green operator
exact reduced range
relative finite-volume Poincaré estimates
```

These results provide downstream operator theory. They do **not** by themselves supply a scale-independent lower bound for the physical gap.

---

# 4. Local continuous-vacuum Harnack and one-link Doob control

The current model-facing route includes a genuinely local, volume-independent Wilson estimate.

The canonical chain proves, in particular,

```text
one-link Wilson-action oscillation is uniformly bounded
  -> one-slab kernel ratio <= exp(8 beta)
  -> continuous positive-vacuum local Harnack control
  -> Doob one-link conditional law
  -> centered one-link resampling gap = 1
  -> raw Wilson variance * exp(-16 beta)
       <= continuous-vacuum Doob variance
```

For bounded continuous Wilson observables this is connected to the native conditional variance and the global Gibbs `L²` one-link projection defect.

This local theorem is a real quantitative input. The remaining challenge is to assemble such local information into the required global/scale-uniform twelve-spatial `L²` coercivity without inserting an unjustified norm-equivalence or Dobrushin-to-Poincaré shortcut.

---

# 5. The genuine twelve-spatial conditional-expectation family

On the actual one-slab ground-state joint `L²` carrier, the repository constructs

```text
P₀,...,P₅ = six right-boundary spatial conditional expectations
L₀,...,L₅ = six left-boundary spatial conditional expectations
```

Each is a genuine Hilbert-space conditional-expectation projection. They are combined into one twelve-color family on the same carrier.

The retained-coordinate program then establishes the exact qualitative geometry rather than assuming it:

```text
right six retained coordinate supports
  -> left-boundary sigma information

left six retained coordinate supports
  -> right-boundary sigma information

actual ground-state null sets
  <-> pair-Haar null sets

right-six fixed and left-six fixed
  -> pair-Haar coordinate measurability from both boundaries
  -> two-boundary product collapse
  -> a.e. constancy
```

PR #3746 closes the qualitative endpoint:

```text
fixed by all genuine 12 spatial conditional expectations
  <-> ground-state-a.e. constant.
```

No quantitative Poincaré coefficient is inferred from this statement.

---

# 6. Exact twelve-spatial residual kernel

Let the conventional twelve-spatial Dirichlet/residual energy be

```text
E₁₂(z) = (1/12) Σ_c ||z - P₁₂,c z||².
```

The recent canonical sequence is:

| PR | Canonical result |
|---|---|
| #3746 | genuine twelve-color common-fixed sector = ground-state-a.e. constants |
| #3768 | `E₁₂(z)=0` iff the represented function is ground-state-a.e. constant |
| #3770 | the a.e.-constant statement is lifted to equality with an actual constant vector in joint `L²` |
| #3773 | the kernel is the intrinsic real constant line; on its orthogonal complement the kernel is `{0}` |
| #3775 | on the genuine physical full-top-orthogonal sector, `E₁₂(R U x)=0` iff `x=0` |

The #3773 step uses the intrinsic Hilbert geometry of the same joint carrier and mathlib's submodule orthogonality machinery. It does not identify unrelated carriers by notation or convention.

The #3775 step closes the formerly missing physical bridge by identifying the transformed positive top vector with constant one in vacuum `L²`, identifying its right-boundary lift with the intrinsic joint constant-one vector, and then using injectivity plus the full top-eigenspace orthogonal geometry.

Crucially, the full top eigenspace remains explicit. No vacuum uniqueness or top-eigenspace simplicity is assumed.

---

# 7. Twelve-spatial Poincaré routing to the physical transfer gap

The repository already contains the exact normalization bridge

```text
E₁₂(z) = 1/2 (E₆,right(z) + E₆,left(z)).
```

On right-boundary lifts all six left updates are fixed, so

```text
E₁₂(Ru) = 1/2 E₆(u).
```

Hence a positive twelve-spatial Poincaré coefficient on the physical top-orthogonal right-lifted sector,

```text
κ ||x||² <= E₁₂(R U x),
```

with the harmless normalization choice `κ <= 1/2`, implies

```text
six-spatial frame coefficient >= 2κ
physical top-eigenspace transfer gap >= 3κ/4.
```

The implication is canonical. The missing theorem is the production of a suitable **scale-independent** `κ` from the actual Wilson/Doob/Harnack geometry.

---

# 8. Present mathematical frontier

The next central target is no longer

```text
identify the twelve-color common-fixed space.
```

That is done.

It is now the quantitative statement

```text
PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts
```

schematically:

```text
∃ κ > 0,
  κ <= 1/2
  and for every scale n and every x in K_n,

  κ ||x||² <= E₁₂,n(R U x).
```

A mathematically valid route must explain why the coercivity constant does not collapse with volume/scale. Candidate ingredients already present in the repository include

```text
explicit local Harnack control
explicit Doob one-link variance comparison
exact conditional-expectation projection identities
finite six-color coordinate elimination
genuine pair-Haar / ground-state null-set transport
physical top-orthogonal qualitative kernel triviality
```

What is still required is a global quantitative gluing/mixing argument strong enough to turn those ingredients into one scale-independent `L²` Poincaré constant.

The following shortcuts are not accepted:

```text
trivial kernel => uniform spectral gap                     false in general
q_n < 1 for every n => inf_n (1-q_n) > 0                  false in general
mutual absolute continuity => uniform L² norm equivalence false without bounds
local TV/Harnack control => global L² Poincaré             needs a theorem
selected vacuum vector => full top eigenspace              not assumed
qualitative AE collapse => quantitative coercivity          needs new analysis
```

---

# 9. Downstream path after uniform coercivity

Once a scale-independent physical twelve-spatial Poincaré coefficient is genuinely proved, the existing theorem network is designed to propagate it through

```text
uniform twelve-spatial Poincaré
  -> uniform physical top-eigenspace transfer gap
  -> uniform non-top resolvent / Green / decay control
  -> stable thermodynamic/scaling passage
  -> physical continuum OS/Hamiltonian spectral lower bound
  -> continuum clustering / spectral consequences
```

This propagation still requires carrier compatibility and same-root limit theorems at each stage. A finite-volume uniform gap is a major milestone, not automatically the final Clay theorem.

---

# 10. What remains for Clay-level completion

Major open obligations include

```text
scale-independent model-derived physical coercivity
controlled thermodynamic / continuum physical limit
full same-root four-dimensional continuum gauge field/state
physical OS/Wightman identification on the relevant continuum carrier
vacuum structure at the required level
strictly positive continuum spectrum above the vacuum
final existence + mass-gap theorem satisfying the Clay formulation
```

The repository intentionally records these as open rather than hiding them behind implication packages.

---

# 11. Authority, provenance, and CI discipline

The theorem-development policy is part of the proof architecture.

For authoritative theorem work:

```text
start from the exact canonical SHA
use the authoritative theorem branch
keep changes additive/tighten-only
never weaken physical assumptions silently
never identify unrelated carriers silently
no sorry / admit / new axiom / placeholder theorem
freeze writes while exact-head CI is running
inspect the first real Lean error before editing a failed head
require terminal workflow success, not queued/in_progress state
fresh-check base/head/mergeability/reviews/threads before merge
normal-merge with expected head SHA
verify the post-merge branch pointer and push CI
```

Pinned environment at the current checkpoint:

```text
Lean    leanprover/lean4:v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

The authoritative theorem checkpoint for this README is

```text
f82275f25c7e33de1410ec1e58b3533097d9383b
```

with merge-push PR Lean Fast Check #13476 completed successfully.

---

# 12. Reading the repository

For the development order and active obligations, see [`ROADMAP.md`](ROADMAP.md).

For external review, the repository also contains audit/replay material such as

```text
EXTERNAL_AUDIT_PACKET.md
EXTERNAL_REVIEW_CHECKLIST.md
INDEPENDENT_REPLAY.md
```

The preferred reading rule is simple:

```text
README/ROADMAP explain the state of the proof.
The authoritative theorem branch and exact SHA determine what is actually proved.
```
