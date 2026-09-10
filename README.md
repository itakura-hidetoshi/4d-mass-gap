# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, ground-state conditional-expectation geometry, and the mass-gap problem.

The repository deliberately separates

1. exact finite periodic compact `SU(N)` Wilson theorems;
2. same-root continuum / Osterwalder--Schrader constructions;
3. finite-volume physical transfer and top-orthogonal operator theory;
4. genuine ground-state joint-law conditional expectations;
5. raw Wilson / heat-bath / Doob locality and comparison theorems;
6. quantitative implication machinery whose decisive scale-uniform input is still open; and
7. the remaining thermodynamic, continuum, and Clay-level obligations.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The qualitative twelve-spatial kernel obstruction is closed: on the genuine physical full-top-orthogonal sector, zero twelve-spatial residual occurs only at zero.
>
> Since that checkpoint, the canonical theorem branch has also closed a concrete same-color Wilson locality chain through exact six-spatial-color heat-bath commutation and an order-independent bounded-continuous Feller color block.
>
> The next unresolved seam is to connect that raw Wilson/Feller same-color block to the **actual vacuum-weighted / ground-state Doob conditional-expectation carrier without adding an abstract independence hypothesis**. Only after that carrier compatibility is explicit can the proof program legitimately build the quantitative same-color block estimate needed for a scale-independent Poincaré/coercivity coefficient.

---

## Repository status — 2026-09-10 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Authoritative exact canonical SHA:
  2e294f5c9f95484c42809048cea4d08f284adba2

Latest canonical theorem merge:
  PR #3791
  Build order-independent six-color spatial Wilson heat-bath block

Canonical merge-push validation:
  PR Lean Fast Check #13491 = completed / success

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

# Current proof picture

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
  -> centered one-link resampling gap = 1
  -> explicit local variance comparison exp(-16 beta)
  -> native Wilson conditional-variance / projection-defect bridge

E. GROUND-STATE TWELVE-SPATIAL LANE

actual ground-state one-slab joint probability law Π
  -> 6 right + 6 left genuine spatial condExp projections
  -> common fixed by all 12 = ground-state-a.e. constants
  -> kernel(E₁₂) = intrinsic real constant line
  -> on physical full-top-orthogonal sector:
       E₁₂(R U x) = 0  <->  x = 0

F. SAME-COLOR WILSON HEAT-BATH LANE

same-color Wilson plaquette separation                         [#3779]
  -> six-spatial-color plaquette separation                   [#3781]
  -> compact plaquette-neighbor / local-action separation     [#3783]
  -> normalized one-link conditional-law locality             [#3787]
  -> exact six-color raw heat-bath commutation                 [#3789]
  -> bounded-continuous Feller commutation
  -> RightCommutative fixed-color update family
  -> permutation-independent finite fold
  -> canonical six-color parallel Feller block                [#3791]

G. CURRENT CARRIER SEAM

raw Wilson/Feller same-color block
  -/-> automatically the ground-state Doob block

Need an explicit theorem derived from the actual vacuum-weighted law:

same color + separation
  -> remote resampling preserves the relevant Doob one-link law
  -> same-color Doob conditional expectations commute
  -> order-independent six-color Doob / ground-state block

H. CURRENT QUANTITATIVE FRONTIER

from actual Wilson/Doob/ground-state geometry prove one scale-independent
κ > 0 with

  κ ||x||² <= E₁₂,n(R U x)

for every scale n and every physical x in K_n.

Then the already-canonical implication machinery routes

  twelve-spatial Poincaré κ
    -> six-spatial frame coefficient 2κ
    -> physical top-eigenspace transfer gap >= 3κ/4
    -> scale-uniform positive physical transfer gap

I. DOWNSTREAM CONTINUUM / CLAY COMPLETION

uniform finite-volume physical gap
  -> stable thermodynamic/scaling control                 [OPEN]
  -> physical continuum carrier / OS-Wightman link        [OPEN]
  -> positive continuum spectrum above vacuum             [OPEN]
  -> full 4D Yang--Mills existence + mass gap             [OPEN]
```

The current conceptual boundary is therefore

```text
qualitative common-fixed identification                     DONE
physical twelve-spatial kernel triviality                  DONE
same-color raw Wilson conditional locality                 DONE
same-color raw heat-bath commutation                       DONE
order-independent six-color raw/Feller heat-bath block     DONE
same-color ground-state Doob compatibility                 OPEN
scale-independent quantitative coercivity                  OPEN
```

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
reflection geometry and finite Wilson reflection positivity
gauge covariance of plaquette holonomy
gauge invariance of normalized trace observables
integer temporal translation and reflection covariance
spatial-slice and boundary Haar-L² carriers
one-slab Wilson kernels
normalized physical transfer operators
```

The interacting Wilson law is not replaced by product Haar at nonzero coupling unless an explicit theorem performs the required comparison or transport.

---

# 2. Same-root continuum OS construction

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

These results provide downstream operator theory. They do **not** by themselves supply a scale-independent physical gap.

---

# 4. Local continuous-vacuum Harnack and one-link Doob control

The model-facing local route contains a genuinely volume-independent Wilson estimate:

```text
one-link Wilson-action oscillation bound
  -> one-slab kernel ratio <= exp(8 beta)
  -> continuous positive-vacuum local Harnack control
  -> Doob one-link conditional law
  -> centered one-link resampling gap = 1
  -> raw Wilson variance * exp(-16 beta)
       <= continuous-vacuum Doob variance
```

For bounded continuous Wilson observables this is connected to the native conditional variance and global Gibbs `L²` one-link projection defect.

The local constant is useful but is not, by itself, a global same-color factorization theorem or a scale-uniform Poincaré inequality.

---

# 5. Genuine twelve-spatial conditional-expectation geometry

On the actual one-slab ground-state joint `L²` carrier the repository constructs six right-boundary and six left-boundary genuine conditional-expectation projections.

The qualitative chain is now complete:

```text
#3746  common fixed by all 12 = ground-state-a.e. constants
#3768  E₁₂(z)=0 iff represented function is ground-state-a.e. constant
#3770  a.e. constant iff equality with an actual constant vector in joint L²
#3773  kernel(E₁₂) = intrinsic real constant line
#3775  on the genuine physical full-top-orthogonal sector,
       E₁₂(R U x)=0 iff x=0
```

No positive Poincaré coefficient is inferred merely from this trivial-kernel statement.

---

# 6. New same-color Wilson heat-bath chain

The theorem sequence after #3775 closes the concrete locality prerequisites that were previously only prospective.

| PR | Canonical result |
|---|---|
| #3779 | distinct same-colored physical links cannot share a Wilson plaquette |
| #3781 | the separation descends to the actual six spatial color classes |
| #3783 | six-color separation is connected to compact Wilson plaquette-neighbor and local-action locality |
| #3787 | the exact normalized target one-link conditional law is unchanged by remote same-color resampling |
| #3789 | exact pointwise/function-level six-color Wilson heat-bath transforms commute |
| #3791 | the commutation is lifted to the bounded-continuous Feller carrier and assembled into an order-independent parallel fixed-color block |

The #3791 block is mathematically concrete: the one-link update family is `RightCommutative`, `List.Perm.foldl_eq` gives permutation invariance, and a canonical full-color block is defined by updating every link in the selected six-color class exactly once.

This route uses the actual compact Wilson conditional measures and the existing replacement geometry. It does **not** introduce a new abstract independence hypothesis.

---

# 7. The present carrier obstruction: Wilson/Feller versus ground-state Doob

The current raw same-color commutation theorem is not silently promoted to the genuine ground-state Doob carrier.

The reason is structural. The vacuum-weighted one-link law is schematically

```text
μ^Ω_{e,A}(dg) ∝ Ω(A[e <- g]) μ_{e,A}(dg).
```

Even if the raw Wilson conditional law `μ_{e,A}` is unchanged by a remote same-color update, the vacuum factor must also be transported correctly before one may conclude invariance of `μ^Ω_{e,A}`.

Therefore the next exact bridge should have the form

```text
same color + distinct links + actual Wilson separation
  -> vacuum-weighted one-link law is compatible with remote resampling
  -> same-color Doob conditional expectations commute
  -> genuine six-color Doob block is order-independent
```

If the relevant carrier already exists under different notation, it must be connected by an explicit theorem. Unrelated Gibbs, Feller, vacuum-`L²`, and ground-state joint carriers are not identified by convention.

---

# 8. Quantitative target after the Doob carrier seam

The decisive quantitative target remains the scale-family estimate

```text
∃ κ > 0,
  κ <= 1/2,
  and for every scale n and every x in the physical top-orthogonal sector K_n,

  κ ||x||² <= E₁₂,n(R U x).
```

The existing canonical normalization/routing gives

```text
E₁₂(right lift) = 1/2 * E₆(right)

uniform twelve-spatial Poincaré κ
  -> uniform six-spatial frame coefficient 2κ
  -> physical top-eigenspace transfer gap >= 3κ/4.
```

The newly integrated six-color heat-bath commutation is an important structural prerequisite for a genuine block-dynamics or variance-decomposition argument. It is not yet the quantitative lower bound itself.

Potentially valid next mechanisms include an exact block conditional-expectation comparison, martingale/variance decomposition, block contraction theorem, canonical-path estimate, or another rigorous global mixing argument derived from the actual Wilson/Doob structure.

---

# 9. Forbidden shortcuts

The repository keeps the following distinctions explicit:

```text
trivial kernel => uniform spectral gap                     false in general
q_n < 1 for every n => inf_n (1-q_n) > 0                  false in general
mutual absolute continuity => uniform L² norm equivalence false without bounds
raw Wilson locality => Doob locality                       needs vacuum-weight transport
pairwise commutation => quantitative Poincaré             needs an estimate
local Harnack/TV control => global L² Poincaré             needs a theorem
selected vacuum vector => full top eigenspace              not assumed
finite-volume theorem => continuum theorem                 requires a limit theorem
same-root scalar continuum => full 4D gauge field          not the same claim
```

---

# 10. Downstream path after uniform coercivity

Once a scale-independent physical twelve-spatial Poincaré coefficient is genuinely proved, the existing theorem network is designed to propagate it through

```text
uniform twelve-spatial Poincaré
  -> uniform physical top-eigenspace transfer gap
  -> uniform non-top resolvent / Green / decay control
  -> stable thermodynamic/scaling passage
  -> physical continuum OS/Hamiltonian spectral lower bound
  -> continuum clustering / spectral consequences
```

Every step still requires same-root carrier compatibility. A uniform finite-volume transfer gap is a major milestone, not automatically the final Clay theorem.

---

# 11. What remains for Clay-level completion

Major open obligations include

```text
explicit ground-state Doob same-color compatibility
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

# 12. Authority, provenance, and CI discipline

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

The authoritative theorem checkpoint for this README is

```text
2e294f5c9f95484c42809048cea4d08f284adba2
```

with merge-push `PR Lean Fast Check #13491` completed successfully.

---

# 13. Reading the repository

For the development order and active obligations, see [`ROADMAP.md`](ROADMAP.md).

For external review, the repository also contains audit/replay material such as

```text
EXTERNAL_AUDIT_PACKET.md
EXTERNAL_REVIEW_CHECKLIST.md
INDEPENDENT_REPLAY.md
```

Preferred reading rule:

```text
README/ROADMAP explain the state and intended route.
The authoritative theorem branch and exact SHA determine what is actually proved.
```