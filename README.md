# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory starting from the actual periodic compact `SU(N)` Wilson lattice model and following the chain through Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional-expectation geometry, and quantitative mass-gap mechanisms.

The repository is deliberately strict about carrier identity and proof status. Fixed-volume positivity is not called scale-uniform coercivity; a trivial kernel is not called a positive spectral gap; an abstract measurable fiber is not silently called an RCD; and a local Harnack estimate is not promoted to a global Poincare inequality without a theorem that performs that transport.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The present canonical theorem chain does, however, reach a new quantitative point. A single right-boundary target-link update of the literal one-slab Wilson kernel satisfies the sharp volume-independent pairwise Harnack estimate
>
> ```text
> K(A, B[target <- g]) <= exp(8 beta) * K(A, B[target <- h])
> ```
>
> for `0 <= beta`, and the same `exp(8 beta)` comparison has now been transported to the canonical **continuous physical vacuum representative**. The transport is not obtained by identifying an `L2` equivalence class with a pointwise function: it passes through the already-formalized RKHS synthesis representation and a pointwise raw-kernel integral eigen-equation.
>
> The immediate frontier is to compose these two pointwise Harnack controls on the exact carrier of the already-constructed direct ground-state one-link fiber, obtain an explicit pairwise comparison for its weight, normalize that comparison with full denominator control, and then turn the resulting one-link estimate into genuine joint conditional-variance control and finally scale-uniform twelve-spatial coercivity **without inverse-volume loss**.

---

## Repository status — 2026-09-12 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Authoritative exact canonical theorem SHA:
  015d3cceb59e696f692b6d67e017b3aee4664715

Latest theorem merge:
  PR #3887
  Transport sharp one-link Harnack to continuous physical vacuum

Validated theorem head before merge:
  6b281139612a2c1188f2b6a616b2e1d986fb51c6

Exact-head validation:
  PR Lean Fast Check #13589
  completed / success

Post-merge validation:
  PR Lean Fast Check #13590
  completed / success

Public landing/docs branch:
  main

Public main before this documentation refresh:
  28903c1769b7a0979e6e4d7823e50f90cd36b696

Lean:
  leanprover/lean4:v4.30.0-rc2

Mathlib:
  5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative theorem status. `main` is the public landing/documentation surface and is intentionally distinct from theorem authority.

---

# Proof state in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> normalized Haar / Wilson action / Gibbs law
  -> reflection positivity and boundary geometry
  -> literal one-slab Wilson kernel
  -> normalized physical transfer
  -> positive / strictly-positive ground-state structure             [INTEGRATED]

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson scalar readout
  -> rational-time / continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> graph-closed self-adjoint Hamiltonian
  -> normalized vacuum and complete vacuum-orthogonal sector         [INTEGRATED]

C. FINITE PHYSICAL TRANSFER / PAIR LANE

full normalized-transfer top eigenspace F
  -> K = F^perp
  -> completed TT + NN physical pair carrier
  -> strict fixed-volume non-top contraction
  -> decay / resolvent / Green / finite-volume relative Poincare     [INTEGRATED]

D. GROUND-STATE TWELVE-SPATIAL LANE

actual one-slab ground-state joint probability law
  -> 6 right + 6 left genuine spatial condExp projections
  -> common fixed sector = ground-state-a.e. constants
  -> kernel(E12) = intrinsic real constant line
  -> E12(R U x) = 0 <-> x = 0 on genuine physical K                 [INTEGRATED]

E. SAME-COLOR / ONE-LINK GEOMETRY

same-color Wilson plaquette separation
  -> raw one-link locality and heat-bath commutation
  -> fixed-color Feller block
  -> genuine joint target condExp
  -> target residual <= containing color residual                    [INTEGRATED]

F. EXPLICIT GROUND-STATE ONE-LINK FIBER

target/off-target Haar split
  -> a.e. measurable finite-positive fibers
  -> normalized target probability fibers
  -> measurable Markov-kernel representative
  -> exact global lintegral identity
  -> original-coordinate transport
  -> direct SU(N) target-coordinate bridge
  -> direct ground-state one-link Wilson/vacuum weight               [INTEGRATED]

G. TARGET-LOCAL WILSON FACTORIZATION

right target update of one-slab action
  -> exact target-local action variation
  -> exact division-free kernel multiplier
  -> named localFactor = exp(-beta * DeltaS_targetLocal)
  -> exp(-8 beta) <= localFactor <= exp(8 beta)                       [INTEGRATED]

H. PAIRWISE HARNACK CHAIN

direct ground-state weight -> localFactor bridge                     [#3883]
localFactor(g) <= exp(16 beta) * localFactor(h)                       [#3884]
K(A,B[g]) <= exp(8 beta) * K(A,B[h])                                 [#3885]
RKHS synthesis = raw-kernel integral                                 [#3887]
continuous physical vacuum integral eigen-equation                   [#3887]
Omega_c(B[g]) <= exp(8 beta) * Omega_c(B[h])                         [#3887]
                                                                         [INTEGRATED]

I. CURRENT QUANTITATIVE SEAM

kernel Harnack + continuous-vacuum Harnack
  -> direct ground-state one-link weight pairwise Harnack            [OPEN NOW]
  -> normalized target-fiber density comparison / minorization       [OPEN NEXT]
  -> genuine joint one-link conditional-variance lower bound         [OPEN NEXT]
  -> color/twelve-spatial coercivity without inverse-volume loss     [OPEN NEXT]

J. SCALE-UNIFORM TARGET

there exists kappa > 0, independent of scale n, such that

  kappa ||x||^2 <= E12,n(R U x)

for every scale n and every physical x in K_n.                       [OPEN]

Existing implication machinery then gives

  twelve-spatial Poincare kappa
    -> six-spatial frame coefficient 2 kappa
    -> physical transfer gap >= 3 kappa / 4.

K. DOWNSTREAM CONTINUUM / CLAY COMPLETION

uniform finite-volume physical gap
  -> controlled thermodynamic / scaling limit                        [OPEN]
  -> full physical continuum OS/Wightman carrier                     [OPEN]
  -> strictly positive continuum spectrum above vacuum               [OPEN]
  -> full 4D Yang--Mills existence + mass gap                         [OPEN]
```

---

# 1. Actual periodic compact `SU(N)` Wilson root

The finite model uses the genuine compact gauge group

```lean
Matrix.specialUnitaryGroup (Fin N) Complex
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law. The formalized root contains oriented lattice and plaquette geometry, Wilson action and Gibbs measure, reflection positivity, gauge-covariant holonomy, gauge-invariant trace observables, boundary/spatial-slice carriers, one-slab kernels, and normalized physical transfer operators.

The interacting Wilson law is not replaced by product Haar at nonzero coupling unless an explicit theorem provides the required transport or comparison.

---

# 2. Same-root continuum OS construction

A same-root scalar continuum OS lane is built from actual finite Wilson pushforwards. It includes rational-time path laws, subsequential continuum probability laws, continuum reflection positivity, OS quotient/completion, a real strongly continuous contraction semigroup, a graph-closed self-adjoint Hamiltonian, a normalized vacuum, and the complete vacuum-orthogonal sector.

This is a genuine continuum observable process, but it is **not** yet the full four-dimensional continuum gauge field required by the Clay formulation.

---

# 3. Fixed-volume physical transfer theory

At fixed finite volume the repository contains a top/non-top operator-theoretic package: top eigenspace, top-orthogonal sector, completed pair decomposition, strict non-top contraction, power decay, strong convergence, coercivity/spectral confinement, resolvent estimates, Green operators, and relative finite-volume Poincare machinery.

The key limitation remains

```text
q_n < 1 for every fixed n
```

does not imply

```text
inf_n (1 - q_n) > 0.
```

The missing model-facing input is still a **scale-uniform** quantitative lower bound.

---

# 4. Qualitative twelve-spatial closure

The genuine ground-state one-slab joint carrier supports six right and six left conditional-expectation projections. The canonical qualitative chain proves that the common fixed sector is the ground-state-a.e. constant sector, identifies `kernel(E12)` with the intrinsic real constant line, and closes

```text
E12(R U x) = 0 <-> x = 0
```

on the genuine physical full-top-orthogonal sector.

This solves the qualitative kernel problem. It does **not** by itself yield a positive coercivity constant, let alone a scale-independent one.

---

# 5. Explicit ground-state one-link fiber and Markov layer

The earlier abstract disintegration obstacle has been replaced by a concrete same-root construction. The canonical chain contains target/off-target Haar splitting, a.e. target-section measurability, a.e. positive finite fiber mass, normalized probability fibers, an exact normalization identity, a measurable normalized Markov-kernel representative, an exact global lintegral identity, transport to the original complete-right coordinates, and a measurable singleton-target equivalence with the direct `SU(N)` coordinate.

The direct target-coordinate layer then exposes the ground-state one-link weight in terms of transfer normalization, vacuum factors, and the literal one-slab Wilson kernel.

**Claim boundary:** a measurable normalized fiber is not silently renamed a regular conditional distribution unless that exact identification is separately proved.

---

# 6. Target-local Wilson factorization

The canonical target-link chain is

```text
#3863  right-target update of the one-slab action
#3866  target-link crossing-action localization
#3869  intrinsic spatial target-link action localization
#3874  complete target-local one-slab action variation
#3877  exact division-free multiplicative kernel update
#3880  named local Boltzmann factor + uniform pointwise bounds
```

For `0 <= beta`, the named multiplier satisfies

```text
localFactor = exp(-beta * DeltaS_targetLocal)

exp(-8 beta) <= localFactor <= exp(8 beta).
```

The constant `8` comes from the finite target-touching Wilson geometry and is independent of the lattice volume.

---

# 7. From local factors to sharp pairwise Harnack

The next canonical steps sharpen the form in which that local control can be used.

| PR | Integrated result |
|---|---|
| #3883 | bridges the direct ground-state one-link fiber weight to the target-local factorization |
| #3884 | proves the symmetric pairwise local-factor comparison with factor `exp(16 beta)` |
| #3885 | proves the sharper raw-kernel comparison `K(A,B[g]) <= exp(8 beta) K(A,B[h])` and its symmetric form |
| #3887 | proves the RKHS synthesis/raw-kernel integral bridge, the pointwise continuous-vacuum integral eigen-equation, and the continuous-vacuum Harnack comparison with factor `exp(8 beta)` |

The `#3885` estimate is stronger than merely combining the upper and lower bounds of `#3880`: it rebases the exact kernel factorization at the comparison value and keeps the constant at `exp(8 beta)`.

---

# 8. Why PR #3887 matters

The physical vacuum starts life in an `L2` setting, so a pointwise Harnack theorem cannot be justified by simply evaluating an almost-everywhere eigenvector identity. The canonical route instead uses the already-existing continuous physical vacuum representative.

The new bridge proves schematically

```text
<Analysis(f), Feature(B)>
  = integral_A f(A) * K(A,B) dmu(A),
```

and therefore gives the pointwise eigen-equation

```text
||T_phys|| * Omega_c(B)
  = integral_A Omega(A) * K(A,B) dmu(A).
```

Using the a.e. nonnegativity of the canonical nonnegative top eigenvector, the raw kernel Harnack inequality passes through the integral, and positivity of `||T_phys||` allows cancellation. Thus

```text
Omega_c(B[g]) <= exp(8 beta) * Omega_c(B[h])
```

holds pointwise for arbitrary target values `g,h`, together with the symmetric reverse comparison.

No unjustified identification of an OS vacuum class with a pointwise eigenfunction is used.

---

# 9. Immediate mathematical frontier

The direct ground-state one-link weight already has an exact Wilson/vacuum factorization. The raw kernel and the canonical continuous physical vacuum now each have a volume-independent `exp(8 beta)` pairwise comparison.

The next decisive theorem should therefore work **on the exact direct-fiber carrier** and prove a pairwise comparison for the complete one-link weight. The natural product estimate suggests an `exp(16 beta)` scale for the two varying factors, but that constant must be obtained by an explicit Lean theorem after verifying the exact vacuum-representative bridge used in the direct fiber; it is not treated as automatic.

After the unnormalized weight comparison is proved, normalization must be handled explicitly. The desired next layer is schematically

```text
unnormalized direct target weight comparison
  -> numerator and denominator control
  -> normalized target-fiber density comparison
  -> volume-independent Harnack / minorization
  -> quantitative conditional-variance bound.
```

No hidden denominator cancellation and no unproved RCD identification are allowed.

---

# 10. From one-link information to scale-uniform coercivity

The genuine joint one-link conditional expectation already satisfies the monotonicity needed to feed a target-link estimate into its containing color residual. The difficult step is quantitative globalization: local information must be converted into a six-color / twelve-spatial lower bound without paying a factor proportional to the number of links.

The target remains

```text
exists kappa > 0, independent of n,
  forall n x in K_n,
    kappa * ||x||^2 <= E12,n(R U x).
```

Once such a model-derived `kappa` exists, the already-formalized implication chain yields the six-spatial frame coefficient `2 kappa` and a physical transfer-gap lower bound `3 kappa / 4`.

---

# Permanent logical boundaries

The following distinctions are permanent repository invariants:

```text
finite-volume theorem != continuum theorem
trivial kernel != quantitative coercivity
q_n < 1 for all n != inf_n (1 - q_n) > 0
raw Wilson locality != vacuum-weighted Doob locality without transport
measurable normalized fiber != RCD unless proved
unnormalized Harnack != normalized minorization without denominator control
one-link comparison != global Poincare without a globalization theorem
pairwise commutation != Poincare lower bound
selected vacuum vector != full top eigenspace
same-root scalar continuum != full 4D continuum Yang--Mills field
green open PR != merged canonical theorem
public main != theorem authority
```

---

# Verification discipline

The theorem carrier follows exact-SHA proof discipline:

```text
start from the exact authoritative canonical SHA
work additively / tighten-only
forbid sorry / admit / new axioms / placeholder theorems
freeze writes during exact-head CI
accept only terminal completed/success validation
fresh-check base, head, mergeability, and branch pointer before merge
normal-merge with the expected exact head SHA
verify merge parents, theorem-branch pointer, and post-merge CI
```

Pinned environment:

```text
Lean    leanprover/lean4:v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

For development and replay, use the repository's pinned Lake environment; the standard whole-project check is

```bash
lake build
```

See also [`ROADMAP.md`](ROADMAP.md), [`PHYSICAL_REALIZATION_BOUNDARY.md`](PHYSICAL_REALIZATION_BOUNDARY.md), [`CONTRIBUTING.md`](CONTRIBUTING.md), and [`CITATION.cff`](CITATION.cff).
