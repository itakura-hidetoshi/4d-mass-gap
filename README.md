# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, ground-state conditional-expectation geometry, and the mass-gap problem.

The repository is organized around a strict distinction between what is already formalized on an exact carrier and what remains open. In particular, finite-volume positivity, qualitative kernel triviality, local Harnack control, raw Wilson heat-bath commutation, and continuum mass-gap conclusions are not silently identified with one another.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The qualitative twelve-spatial kernel problem is closed on the genuine physical full-top-orthogonal sector. The raw Wilson same-color locality/heat-bath chain is also formalized, and the Doob remote-replacement law has been reduced to an explicit vacuum-weight obstruction. Most recently, a genuine one-link conditional-expectation geometry has been constructed directly on the ground-state one-slab joint `L²` carrier, with the exact monotonicity
>
> ```text
> one-link residual <= containing six-color residual.
> ```
>
> The immediate mathematical frontier is therefore no longer merely “prove same-color Doob commutation.” The more direct route is to identify or quantitatively compare the **actual ground-state joint one-link conditional law / conditional variance** with the already-formalized physical one-link Doob fiber, and then derive a block/global estimate without losing a volume-dependent factor.

---

## Repository status — 2026-09-10 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Authoritative exact canonical theorem SHA:
  c0cda8667a3d94eb2576ac602a93943980c9c0c3

Latest theorem merge:
  PR #3798
  Add ground-state joint one-link conditional expectation geometry

Validated theorem head before merge:
  d5abb70632ea4429041732d88a795dcf4e40592f

Post-merge validation:
  PR Lean Fast Check #13502
  completed / success

Public landing/docs branch:
  main

Lean:
  leanprover/lean4:v4.30.0-rc2

Mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status. `main` is the public landing/documentation surface and is intentionally kept distinct from the theorem carrier.

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
  -> finite-volume relative Poincaré and spectral-exclusion machinery

D. LOCAL WILSON / DOOB / HARNACK LANE

continuous positive physical vacuum
  -> one-link replacement geometry
  -> volume-independent local Harnack ratio exp(8 beta)
  -> physical one-link Doob conditional law
  -> centered one-link resampling gap = 1
  -> explicit local variance comparison exp(-16 beta)
  -> native Wilson conditional-variance / projection-defect bridge

E. GROUND-STATE TWELVE-SPATIAL LANE

actual one-slab ground-state joint probability law Π
  -> 6 right + 6 left genuine spatial condExp projections
  -> common fixed by all 12 = ground-state-a.e. constants
  -> kernel(E12) = intrinsic real constant line
  -> on the genuine physical full-top-orthogonal sector:
       E12(R U x) = 0  <->  x = 0

F. SAME-COLOR WILSON / DOOB NORMAL-FORM LANE

same-color Wilson plaquette separation                         [#3779]
  -> actual six-spatial-color separation                      [#3781]
  -> compact Wilson local-action separation                   [#3783]
  -> normalized raw one-link conditional-law locality         [#3787]
  -> exact same-color raw heat-bath commutation               [#3789]
  -> order-independent fixed-color raw/Feller block           [#3791]
  -> remote-replacement Doob law normal form                  [#3795]
       = same raw target law + explicit two-link Ω weight

G. GENUINE JOINT ONE-LINK CONDITIONAL EXPECTATION

ground-state joint one-slab L²
  -> retain full left boundary + right boundary off one target
  -> genuine one-link condExpL2 projection                    [#3798]
  -> off-color sigma algebra <= off-target sigma algebra
  -> Hilbert projection nearest-point monotonicity
  -> ||f - P_target f|| <= ||f - P_color(target) f||
  -> squared one-link defect <= containing color defect

H. CURRENT QUANTITATIVE SEAM

physical one-link Doob fiber variance
  -/-> exact genuine ground-state joint one-link defect

Need an explicit same-root theorem such as:

  joint one-link disintegration identity
or
  quantitative Doob-fiber -> joint-one-link comparison.

Then one must globalize without a volume-dependent loss:

  local one-link information
    -> six-color / twelve-spatial block estimate
    -> scale-independent κ > 0

I. TARGET

for every scale n and every physical x in K_n,

  κ ||x||² <= E12,n(R U x)

with one κ > 0 independent of n.

Existing implication machinery then gives

  twelve-spatial Poincaré κ
    -> six-spatial frame coefficient 2κ
    -> physical transfer gap >= 3κ/4.

J. DOWNSTREAM CONTINUUM / CLAY COMPLETION

uniform finite-volume physical gap
  -> stable thermodynamic/scaling control                 [OPEN]
  -> physical continuum carrier / OS-Wightman link        [OPEN]
  -> positive continuum spectrum above vacuum             [OPEN]
  -> full 4D Yang--Mills existence + mass gap             [OPEN]
```

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite model uses the genuine compact gauge group

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law. The formalized root includes oriented lattice and plaquette geometry, Wilson action and Gibbs measure, reflection positivity, gauge-covariant holonomy, gauge-invariant trace observables, boundary/spatial-slice carriers, one-slab kernels, and normalized physical transfer operators.

The interacting Wilson law is not replaced by product Haar at nonzero coupling unless an explicit theorem provides the transport or comparison.

---

# 2. Same-root continuum OS construction

A same-root scalar continuum OS lane is built from actual finite Wilson pushforwards. It includes rational-time path laws, subsequential continuum probability laws, continuum reflection positivity, OS quotient/completion, a real strongly continuous contraction semigroup, a graph-closed self-adjoint Hamiltonian, a normalized vacuum, and the complete vacuum-orthogonal sector.

This is a genuine continuum observable process, but it is **not** yet the complete four-dimensional continuum gauge field required by the Clay formulation.

---

# 3. Finite-volume physical transfer theory

At fixed finite volume the repository has a completed top/non-top operator-theoretic package: top eigenspace, top-orthogonal sector, completed pair decomposition, strict non-top contraction, power decay, strong convergence, coercivity, spectral confinement, resolvent estimates, Green operator, and relative finite-volume Poincaré estimates.

The essential limitation is permanent:

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

The continuous-vacuum route contains a volume-independent local Harnack estimate. Schematically,

```text
R^{-1} Ω(A) <= Ω(A[e <- g]) <= R Ω(A),
R = exp(8 beta),
```

which yields a quantitative comparison between the raw Wilson one-link variance and the physical Doob one-link variance, with the canonical factor `exp(-16 beta)` in the lower comparison direction.

This is a strong local theorem. It is not a global Poincaré inequality and does not itself identify the physical Doob fiber with the conditional law of the ground-state joint measure.

---

# 5. Qualitative twelve-spatial kernel closure

The genuine ground-state one-slab joint carrier supports six right and six left conditional-expectation projections. The canonical qualitative chain now includes

```text
#3746  common fixed by all 12 = ground-state-a.e. constants
#3768  E12(z)=0 iff represented function is ground-state-a.e. constant
#3770  a.e. constant iff equality with an actual constant vector in joint L²
#3773  kernel(E12) = intrinsic real constant line
#3775  on the genuine physical full-top-orthogonal sector,
       E12(R U x)=0 iff x=0
```

This proves qualitative injectivity of the twelve-spatial residual on the relevant physical sector. It does **not** produce a positive uniform lower bound.

---

# 6. Same-color Wilson locality and raw/Feller block

The same-color chain is concrete and model-derived:

| PR | Canonical result |
|---|---|
| #3779 | distinct same-colored physical spatial links cannot share a Wilson plaquette |
| #3781 | separation descends to the actual six spatial color classes |
| #3783 | compact plaquette-neighbor and local-action separation |
| #3787 | exact raw normalized target one-link conditional law is unchanged by remote same-color replacement |
| #3789 | exact same-color raw heat-bath transforms commute |
| #3791 | bounded-continuous Feller commutation and an order-independent full fixed-color update block |
| #3795 | exact remote-replacement normal form for the Doob one-link law |

PR #3795 is especially important for claim discipline. After a remote same-color replacement, the target Doob law is rewritten using the **same raw target Wilson measure** and an explicit two-link vacuum weight. Thus the remaining obstruction to Doob locality is isolated entirely in the vacuum-weight term rather than hidden in the raw Wilson measure.

No abstract independence hypothesis is introduced.

---

# 7. Genuine one-link conditional expectation on the ground-state joint carrier

PR #3798 changes the shape of the active frontier.

For a target spatial link, the repository now defines the sigma algebra retaining

```text
complete left boundary
+ all right-boundary spatial coordinates except the target link.
```

This gives a genuine one-link `condExpL2` projection on the existing ground-state joint `L²` carrier.

Because the off-color sigma algebra is contained in the off-target sigma algebra, Mathlib's Hilbert-space nearest-point theorem for orthogonal projections gives

```text
||f - P_target f|| <= ||f - P_color(target) f||,
```

and hence

```text
||f - P_target f||² <= ||f - P_color(target) f||².
```

This theorem is carrier-safe: it uses the genuine joint law directly and does not identify the raw Feller carrier, vacuum `L²`, and ground-state joint `L²` by convention.

It also shows that same-color Doob commutation is **not logically required** before every quantitative attack. A direct local-to-joint comparison route is now available.

---

# 8. Present obstruction: local one-link control must enter the genuine joint carrier

The next decisive theorem should connect the local physical Doob fiber to the new genuine joint one-link projection. Acceptable forms include an exact conditional-disintegration identity or a quantitative variance comparison derived from the actual ground-state joint density.

The desired bridge is conceptually

```text
physical Doob one-link variance
  -> genuine ground-state joint one-link conditional variance
  = ||f - P_target f||²
  <= containing six-color defect.
```

The arrow must be proved on the actual same-root measure. It must not be inserted as a new independence or carrier-identification assumption.

---

# 9. The second obstruction: avoid volume-dependent globalization loss

The new monotonicity theorem is necessary but not sufficient for a scale-uniform gap. If a color contains many links, inequalities of the form

```text
color defect >= each individual one-link defect
```

do not by themselves imply a volume-independent lower bound by the **sum** of all one-link defects. Naive averaging may introduce a factor proportional to the inverse number of links.

Therefore a successful global argument must contain a genuinely uniform mechanism, for example a block Poincaré estimate, tensorization/approximate tensorization theorem, martingale variance decomposition, comparison of block conditional expectations, canonical-path/frame estimate, or another scale-independent mixing theorem derived from the actual Wilson/Doob structure.

This is now one of the clearest mathematical bottlenecks in the repository.

---

# 10. Quantitative target

The decisive scale-family theorem remains

```text
∃ κ > 0,
  ∀ n,
  ∀ x ∈ K_n,

  κ ||x||² <= E12,n(R U x).
```

The existing theorem network already contains the downstream routing

```text
uniform twelve-spatial Poincaré κ
  -> uniform six-spatial frame coefficient 2κ
  -> physical top-eigenspace transfer gap >= 3κ/4.
```

Thus the main unresolved work is not algebraic propagation after `κ`; it is the production of `κ` from the actual model without a scale-dependent loss.

---

# 11. Forbidden shortcuts

The repository keeps the following implications explicitly invalid unless a theorem supplies the missing hypothesis:

```text
trivial kernel => uniform spectral gap                     false in general
q_n < 1 for every n => inf_n (1-q_n) > 0                  false in general
mutual absolute continuity => uniform L² norm equivalence false without bounds
raw Wilson locality => Doob locality                       needs vacuum-weight control
one-link residual <= color residual => tensorized sum      false without a block estimate
pairwise commutation => quantitative Poincaré              needs an estimate
local Harnack/TV control => global L² Poincaré             needs a theorem
selected vacuum vector => full top eigenspace              not assumed
finite-volume theorem => continuum theorem                 requires a limit theorem
same-root scalar continuum => full 4D gauge field          not the same claim
```

---

# 12. Downstream Clay-level obligations

After a genuine scale-independent physical transfer gap is obtained, the remaining program still includes controlled thermodynamic/scaling passage, a full same-root four-dimensional continuum gauge field/state, physical OS/Wightman identification on the relevant continuum carrier, the required vacuum structure, and a strictly positive continuum spectrum above vacuum.

A uniform finite-volume transfer gap would be a major milestone, not automatically the final Clay theorem.

---

# 13. Authority and CI discipline

For theorem development:

```text
start from the exact authoritative canonical SHA
use the authoritative theorem carrier, not main
keep changes additive/tighten-only
never weaken physical assumptions silently
never identify unrelated carriers silently
no sorry / admit / new axiom / placeholder theorem
freeze writes while exact-head CI is running
inspect the first genuine Lean error before editing a failed head
require terminal workflow success
fresh-check base/head/mergeability/reviews/threads before merge
normal-merge with expected head SHA
verify merge parents, theorem-branch pointer, and post-merge push CI
```

The authoritative theorem checkpoint represented by this README is

```text
formal/real-hilbert-uniform-coercive-strong-limit
@ c0cda8667a3d94eb2576ac602a93943980c9c0c3
```

with post-merge `PR Lean Fast Check #13502 = completed / success`.

For the detailed order of the next proof units, see [`ROADMAP.md`](ROADMAP.md).
