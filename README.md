# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory through the actual periodic compact `SU(N)` Wilson lattice model, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional-expectation geometry, and quantitative mass-gap mechanisms.

The repository keeps a strict boundary between what has been formalized on an exact carrier and what remains open. In particular, the following are never silently identified:

- fixed-volume positivity and scale-uniform coercivity;
- trivial kernel and a positive spectral gap;
- raw Wilson one-link locality and vacuum-weighted Doob locality;
- a measurable normalized fiber and a regular conditional distribution;
- a local Harnack bound and a global Poincare inequality;
- a same-root scalar continuum process and the full four-dimensional continuum gauge field required by the Clay problem.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The qualitative twelve-spatial kernel problem is closed on the genuine physical full-top-orthogonal sector. The same-color raw Wilson locality / heat-bath chain is formalized. The ground-state one-link program has now advanced far beyond the first conditional-expectation step: the repository contains explicit target/off-target Haar splitting, a.e. measurable and finite-positive target fibers, normalized probability fibers, a measurable Markov-kernel representative with exact global integral identity, transport back to the original right-boundary coordinates, an exact bridge to the direct `SU(N)` target coordinate, and an explicit Wilson/vacuum factorization of the direct one-link weight.
>
> Most recently, a single right-boundary target-link update of the literal one-slab Wilson kernel was factorized by a named target-local Boltzmann multiplier, and that multiplier was proved to satisfy the volume-independent deterministic bounds
>
> ```text
> exp(-8 beta) <= localFactor <= exp(8 beta)
> ```
>
> for `0 <= beta`.
>
> The immediate frontier is therefore to turn this exact local factorization and its uniform bounds into a normalized one-link comparison / minorization theorem on the already-constructed ground-state fiber, then propagate that quantitative one-link information into a color/twelve-spatial coercivity estimate **without an inverse-volume loss**.

---

## Repository status — 2026-09-11 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Authoritative exact canonical theorem SHA:
  f65c0fc75c56ffdcba103331768b8aa73fbfba65

Latest theorem merge:
  PR #3880
  Bound one-slab right target local Boltzmann factor

Validated theorem head before merge:
  6f33df5b7d7f1c4258101b55a7d1372edfb15680

Exact-head validation:
  PR Lean Fast Check #13579
  completed / success

Public landing/docs branch:
  main

Current public main before this documentation refresh:
  a848056054d55bd67f88a7eb743420d4b6207cab

Lean:
  leanprover/lean4:v4.30.0-rc2

Mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status. `main` is the public landing/documentation surface and is intentionally distinct from theorem authority.

---

# Current proof picture

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> Wilson action / normalized Haar / Gibbs law
  -> reflection geometry and OS positivity
  -> boundary / spatial-slice Hilbert carriers
  -> literal one-slab Wilson kernel
  -> normalized physical transfer
  -> positive / strictly-positive ground-state structure

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum and complete vacuum-orthogonal sector

C. FINITE PHYSICAL TRANSFER / PAIR LANE

full normalized-transfer top eigenspace F
  -> K = F^perp
  -> completed physical pair carrier PP = TT + NN
  -> strict fixed-volume non-top contraction
  -> power decay / strong convergence / resolvent / Green operator
  -> finite-volume relative Poincare and spectral exclusion

D. LOCAL PHYSICAL DOOB / HARNACK LANE

continuous positive physical vacuum
  -> one-link replacement geometry
  -> volume-independent local Harnack control
  -> physical one-link Doob conditional law
  -> centered one-link resampling gap = 1
  -> explicit local variance comparison

E. GROUND-STATE TWELVE-SPATIAL LANE

actual one-slab ground-state joint probability law
  -> 6 right + 6 left genuine spatial condExp projections
  -> common fixed by all 12 = ground-state-a.e. constants
  -> kernel(E12) = intrinsic real constant line
  -> on the genuine physical full-top-orthogonal sector:
       E12(R U x) = 0 <-> x = 0

F. SAME-COLOR RAW WILSON BLOCK LANE

same-color plaquette separation
  -> six-spatial-color separation
  -> target-local Wilson action locality
  -> raw one-link conditional-law locality
  -> same-color raw heat-bath commutation
  -> permutation-independent fixed-color Feller block
  -> remote-replacement Doob normal form

G. GROUND-STATE ONE-LINK FIBER / MARKOV LANE

right target/off-target Haar split
  -> literal target fiber measure and mass
  -> a.e. fiber measurability
  -> a.e. 0 < fiberMass < infinity
  -> normalized a.e. target probability fibers
  -> exact fiber normalization identity
  -> measurable Markov-kernel representative
  -> exact global lintegral identity
  -> ground-state split specialization
  -> original complete-right coordinate identity
  -> singleton target <-> direct SU(N) coordinate bridge
  -> normalized split fiber -> direct target coordinate bridge

H. DIRECT TARGET-LOCAL WILSON FACTORIZATION LANE

direct ground-state one-link fiber weight
  -> exact Wilson / left-vacuum / right-vacuum factorization
  -> one-slab right-target action variation decomposition
  -> crossing-action target-link localization
  -> intrinsic spatial target-link action localization
  -> complete target-local one-slab action variation
  -> exact division-free kernel update factorization
  -> named local Boltzmann factor
  -> exp(-8 beta) <= localFactor <= exp(8 beta)

I. CURRENT QUANTITATIVE SEAM

uniform target-local factor bounds
  -> normalized target-fiber comparison / minorization            [OPEN NOW]
  -> one-link conditional-variance lower bound on genuine joint L2 [OPEN NEXT]
  -> color/twelve-spatial block estimate without volume loss       [OPEN NEXT]

J. SCALE-UNIFORM TARGET

there exists kappa > 0, independent of scale n, such that

  kappa ||x||^2 <= E12,n(R U x)

for every scale n and every physical x in K_n.

Existing implication machinery then gives

  twelve-spatial Poincare kappa
    -> six-spatial frame coefficient 2 kappa
    -> physical transfer gap >= 3 kappa / 4.

K. DOWNSTREAM CONTINUUM / CLAY COMPLETION

uniform finite-volume physical gap
  -> stable thermodynamic / scaling control                 [OPEN]
  -> physical continuum carrier / OS-Wightman link          [OPEN]
  -> strictly positive continuum spectrum above vacuum      [OPEN]
  -> full 4D Yang--Mills existence + mass gap                [OPEN]
```

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite model uses the genuine compact gauge group

```lean
Matrix.specialUnitaryGroup (Fin N) Complex
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law. The formalized root includes oriented lattice and plaquette geometry, Wilson action and Gibbs measure, reflection positivity, gauge-covariant holonomy, gauge-invariant trace observables, boundary/spatial-slice carriers, one-slab kernels, and normalized physical transfer operators.

The interacting Wilson law is not replaced by product Haar at nonzero coupling unless an explicit theorem supplies the transport or comparison.

---

# 2. Same-root continuum OS construction

A same-root scalar continuum OS lane is built from actual finite Wilson pushforwards. It includes rational-time path laws, subsequential continuum probability laws, continuum reflection positivity, OS quotient/completion, a real strongly continuous contraction semigroup, a graph-closed self-adjoint Hamiltonian, a normalized vacuum, and the complete vacuum-orthogonal sector.

This is a genuine continuum observable process, but it is **not** yet the full four-dimensional continuum gauge field required by the Clay formulation.

---

# 3. Finite-volume physical transfer theory

At fixed finite volume the repository contains a top/non-top operator-theoretic package: top eigenspace, top-orthogonal sector, completed pair decomposition, strict non-top contraction, power decay, strong convergence, coercivity/spectral confinement, resolvent estimates, Green operator, and relative finite-volume Poincare machinery.

The essential limitation remains:

```text
q_n < 1 for every fixed n
```

does not imply

```text
inf_n (1 - q_n) > 0.
```

The missing model-facing input is scale-uniform quantitative coercivity.

---

# 4. Local physical Doob control

The continuous-vacuum route contains volume-independent local Harnack control and physical one-link Doob resampling estimates. Schematically, local Wilson action oscillation gives a uniform multiplicative comparison of one-link weights; after normalization this controls the corresponding one-link probability law and conditional variance.

This is local information. It is not yet a global twelve-spatial Poincare inequality.

---

# 5. Qualitative twelve-spatial kernel closure

The genuine ground-state one-slab joint carrier supports six right and six left conditional-expectation projections. The canonical qualitative chain contains

```text
#3746  common fixed by all 12 = ground-state-a.e. constants
#3768  E12(z)=0 iff represented function is ground-state-a.e. constant
#3770  a.e. constant iff equality with an actual constant vector in joint L2
#3773  kernel(E12) = intrinsic real constant line
#3775  on the genuine physical full-top-orthogonal sector,
       E12(R U x)=0 iff x=0
```

This closes the qualitative kernel problem. It does **not** produce a positive scale-uniform lower bound.

---

# 6. Same-color Wilson locality and raw block dynamics

The same-color chain is concrete and model-derived:

| PR | Canonical result |
|---|---|
| #3779 | distinct same-colored physical spatial links cannot share a Wilson plaquette |
| #3781 | separation descends to the actual six spatial color classes |
| #3783 | compact Wilson local-action separation |
| #3787 | exact raw target one-link conditional-law locality |
| #3789 | exact same-color raw heat-bath commutation |
| #3791 | permutation-independent fixed-color bounded-continuous/Feller block |
| #3795 | exact remote-replacement normal form for the Doob one-link law |

The #3795 normal form makes the claim boundary explicit: raw Wilson locality removes the raw-measure obstruction, but any further Doob locality theorem must still control the vacuum weight or prove a weaker normalized comparison sufficient for the quantitative estimate.

---

# 7. Genuine joint one-link conditional expectation

PR #3798 constructs the target-link conditional-expectation geometry directly on the actual ground-state joint `L2` carrier. The sigma algebra retains the complete left boundary and every right-boundary spatial coordinate except one target link.

The existing off-color sigma algebra is contained in this off-target sigma algebra, giving

```text
||f - P_target f|| <= ||f - P_color(target) f||
```

and the corresponding squared-energy inequality.

Thus any lower bound on the genuine target one-link residual can feed directly into the containing color residual. The remaining difficulty is not this monotonicity; it is obtaining a quantitative one-link lower bound and globalizing it uniformly.

---

# 8. Ground-state one-link fiber and measurable Markov layer

The former disintegration frontier has been substantially developed.

The canonical sequence now includes:

```text
#3807  expose literal ground-state target fiber measure
#3810  normalize fixed fibers under explicit receipts
#3812  split target/off-target Haar coordinates measure-preservingly
#3815  prove a.e. target-fiber measurability
#3820  prove a.e. finite positive target-fiber mass
#3823  obtain a.e. normalized target probability fibers
#3825  prove exact one-link fiber normalization identity
#3832  construct measurable normalized kernel representative
       + exact global lintegral identity
#3840  prove joint AE measurability in split coordinates
#3842  lift fiber mass to product-a.e. control
#3845  specialize measurable Markov disintegration to the ground-state split
#3848  expose the split-context Haar coordinate equivalence
#3850  transport the Markov identity back to original complete-right coordinates
#3852  identify the singleton target coordinate measurably with direct SU(N)
#3854  bridge split density and mass to the direct gauge coordinate
#3859  push normalized split fiber exactly to the direct target coordinate
#3861  expose the direct one-link Wilson/vacuum weight factorization
```

These theorems remove the earlier obstacle of merely having an abstract `condExpL2` without an explicit one-link fiber model.

**Claim boundary:** the repository still does not silently rename this measurable normalized kernel an RCD or identify it with another pre-existing one-link conditional law unless a theorem states that equality or comparison explicitly.

---

# 9. Exact target-local one-slab kernel factorization

The newest canonical chain localizes a literal right-boundary target-link update inside the one-slab Wilson kernel:

```text
#3863  decompose a right-target update of the one-slab action
#3866  isolate the target-link crossing-action variation
#3869  localize intrinsic spatial target-link action variation
#3874  compose the complete target-local one-slab action variation
#3877  prove the exact division-free multiplicative kernel update
#3880  name the local Boltzmann factor and prove uniform bounds
```

The key exact identity is schematically

```text
K(A, B[target <- g])
  = localFactor(A, B, target, g) * K(A, B),
```

with

```text
localFactor = exp(-beta * DeltaS_targetLocal)
```

and, for `0 <= beta`,

```text
exp(-8 beta) <= localFactor <= exp(8 beta).
```

The constant `8` is inherited from the already-formalized one-link one-slab Wilson action oscillation estimate and is independent of configuration and volume.

This is exactly the kind of model-facing uniform estimate needed for the next Harnack / Doeblin / fiber-comparison step.

What #3880 does **not** yet assert is equally important: no normalized conditional law, no minorization theorem, no contraction, no global Poincare coefficient, no scale-uniform coercivity, and no mass-gap conclusion is obtained merely from the unnormalized factor bound.

---

# 10. Immediate mathematical frontier

The next decisive proof unit should normalize the #3880 target-local factor **inside the already-canonical direct ground-state one-link fiber**.

A useful target theorem has the schematic form

```text
c_-(beta) * nu_reference
  <= nu_ground,target-context
  <= c_+(beta) * nu_reference
```

with explicit constants independent of lattice volume, or an equivalent normalized Harnack / Doeblin minorization statement.

The ingredients are now visible on one exact chain:

```text
direct ground-state fiber density
  = left vacuum * one-slab Wilson kernel * updated-right vacuum

one-slab kernel update
  = target-local factor * base kernel

exp(-8 beta) <= target-local factor <= exp(8 beta).
```

The remaining proof must track the normalization denominator and every vacuum factor on the actual same-root carrier. No hidden cancellation or unjustified conditional-law identification is allowed.

---

# 11. From one-link control to genuine joint residual

Once a normalized one-link comparison / minorization is formalized, the next target is a quantitative lower bound for the genuine joint target projection defect

```text
||f - P_target f||^2.
```

Because PR #3798 already gives

```text
one-link defect <= containing color defect,
```

one obtains a direct route from target-link information into the genuine six-color energy.

The hard direction is quantitative: the one-link estimate must be strong enough to survive the subsequent block/global step with constants independent of volume.

---

# 12. The global obstruction: avoid inverse-volume loss

If a color contains many links, inequalities of the form

```text
color defect >= each individual one-link defect
```

do not by themselves imply a volume-independent lower bound by the **sum** of all one-link defects. Naive averaging can introduce a factor proportional to the inverse number of links.

A successful globalization therefore needs a genuinely uniform mechanism, for example:

- a block Poincare estimate;
- tensorization or approximate tensorization;
- a martingale variance decomposition;
- comparison of block conditional expectations;
- a canonical-path/frame estimate;
- a Dobrushin/Doeblin-style quantitative mixing theorem derived from the actual Wilson/ground-state fibers;
- another model-derived scale-independent block estimate.

This is the principal obstruction between local one-link control and the target scale-uniform physical gap.

---

# 13. Quantitative target

The decisive family theorem remains

```text
there exists kappa > 0 such that
  for every scale n and every x in K_n,

  kappa ||x||^2 <= E12,n(R U x).
```

The downstream routing is already formalized:

```text
uniform twelve-spatial Poincare kappa
  -> uniform six-spatial frame coefficient 2 kappa
  -> physical top-eigenspace transfer gap >= 3 kappa / 4.
```

Thus the present problem is the construction of the uniform `kappa` from the actual Wilson / ground-state model, not algebraic propagation after `kappa` has been supplied.

---

# 14. Forbidden shortcuts

The following implications remain invalid unless a theorem supplies the missing hypothesis:

```text
trivial kernel => uniform spectral gap
q_n < 1 for every n => inf_n (1-q_n) > 0
mutual absolute continuity => uniform L2 norm equivalence
raw Wilson locality => Doob locality
unnormalized local factor bounds => normalized minorization without denominator control
one-link residual <= color residual => tensorized sum over a color
pairwise commutation => quantitative Poincare
local Harnack / TV control => global L2 Poincare
selected vacuum vector => full top eigenspace
finite-volume theorem => continuum theorem
same-root scalar continuum => full 4D Yang--Mills gauge field
```

---

# 15. Downstream Clay-level obligations

After a genuine scale-independent physical transfer gap is obtained, the program still requires controlled thermodynamic/scaling passage, construction or identification of the full same-root four-dimensional continuum gauge field/state, physical OS/Wightman identification on the relevant continuum carrier, the required vacuum structure, and a strictly positive continuum spectrum above vacuum.

A uniform finite-volume transfer gap would be a major theorem, but it is not automatically the final Clay result.

---

# 16. Authority and CI discipline

For theorem development:

```text
start from the exact authoritative canonical SHA
use the authoritative theorem carrier, not main
keep changes additive / tighten-only
never weaken physical assumptions silently
never identify unrelated carriers silently
no sorry / admit / new axiom / placeholder theorem
freeze writes while exact-head CI is running
inspect the first genuine Lean error before editing a failed head
require terminal workflow success
fresh-check base / head / mergeability / reviews / threads before merge
normal-merge with expected head SHA
verify merge parents and theorem-branch pointer after merge
```

The authoritative theorem checkpoint represented by this README is

```text
formal/real-hilbert-uniform-coercive-strong-limit
@ f65c0fc75c56ffdcba103331768b8aa73fbfba65
```

with exact validated theorem head

```text
6f33df5b7d7f1c4258101b55a7d1372edfb15680
```

and

```text
PR Lean Fast Check #13579 = completed / success.
```

For the proof-development order from this point, see [`ROADMAP.md`](ROADMAP.md).
