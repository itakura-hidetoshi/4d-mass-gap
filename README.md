# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional expectations, quantitative mixing, and the mass-gap problem.

The repository is deliberately conservative about claims. It separates finite-volume theorems, almost-everywhere bridges, conditional-law identifications, quantitative coercivity inputs, continuum reconstruction, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current finite-volume program has now crossed the former reference-law disintegration frontier: the normalized continuous-vacuum reference one-link law is represented by a measurable heat-bath kernel; the kernel is proper for the off-fiber sigma algebra; the defining setwise and integral conditional identities are proved; it is identified with conditional expectation and then with Mathlib's regular conditional probability kernel; and its conditional variance is transported to the genuine `condExpKernel` layer.
>
> The newest exact bridge, merged in PR #4080, factors the literal C5 reference fiber law as a continuous-vacuum Doob tilt of a normalized one-slab `local × kernel` raw law. This preserves the important authority boundary that the C5 raw law is **not** silently identified with the full-4D Wilson `singleLinkConditionalMeasure`.
>
> The immediate mathematical frontier is therefore no longer measurability or RCD existence. It is to exploit this exact conditional-law / raw-Doob structure to prove a **distance-sensitive or summable remote influence / covariance estimate** strong enough to remove the link-count obstruction and yield volume-independent same-color block coercivity.

---

## Repository status — 2026-09-14 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Current exact canonical HEAD:
  1696ba98d930c5f59293319fc562d057d4b7586e

This is the normal merge of:
  PR #4080
  Factor C5 reference fiber through one-slab raw Doob law

Exact GREEN theorem head merged by PR #4080:
  154c124671170bdf3975c7e3d1aeb351d9dda026

Exact-head validation:
  PR Lean Fast Check #13798
  workflow run 34787609915
  completed / success

Public landing branch:
  main

Detailed proof order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as canonical theorem status. `main` is a public landing surface and must not be used as theorem authority when the histories differ.

---

# Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> boundary and spatial-slice L2 carriers
  -> normalized physical one-slab transfer
  -> positive / strictly-positive ground-state structure
                                                               [INTEGRATED]

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson gauge-invariant scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Omega and complete Omega-perp
                                                               [INTEGRATED]

C. FINITE PHYSICAL / GROUND-STATE JOINT-LAW LANE

physical top/non-top decomposition
  -> finite-volume contraction / coercivity / resolvent / Green machinery
  -> ground-state one-slab joint probability law
  -> 6 genuine right + 6 genuine left spatial conditional expectations
  -> genuine two-sided 12-spatial family
  -> E12 -> E6 -> raw physical defect -> transfer-gap routing
                                                               [INTEGRATED ROUTING]

D. SHARP ONE-LINK CONTROL

continuous-vacuum complete one-link weight
  -> exp(16 beta) pairwise Harnack                           [#3894]
  -> sharp normalized Haar comparison                       [#3898]
  -> exp(-16 beta) one-link variance lower bound            [#3907]
  -> a.e. compatibility with actual joint split fiber       [#3909]
  -> genuine joint condExpL2 residual on bounded core       [#3921-#3952]
                                                               [INTEGRATED]

E. REMOTE-INFLUENCE DIAGNOSTIC

remote continuous-vacuum weight comparison                  [#3954]
  -> normalized Doob comparison                             [#3959]
  -> bounded-test influence coefficient                     [#3964]
  -> naive same-color row sum carries link-count loss       [#3969]
                                                               [OBSTRUCTION INTEGRATED]

F. LOCALITY -> COVARIANCE ROUTE

raw same-color Wilson local-factor cancellation              [#3978]
  -> source likelihood ratio is source-link local           [#3991, #3994]
  -> four-integral defect = weighted covariance             [#3997, #4000]
  -> target-local x source-local covariance                 [#4004]
  -> canonical positive continuous-vacuum reference weight  [#4011]
  -> normalized reference probability law                  [#4016]
                                                               [INTEGRATED]

G. REFERENCE ONE-LINK DISINTEGRATION

literal normalized one-link fibers                          [#4019]
  -> singleton marginal / exact normalized density          [#4024, #4027]
  -> local normalization identity                           [#4030]
  -> full-law Fubini compatibility                          [#4035]
  -> measurable heat-bath kernel + stationarity             [#4039]
  -> idempotence                                             [#4042]
  -> off-fiber sigma algebra factorization                  [#4045]
  -> proper off-fiber Markov kernel                         [#4048]
  -> setwise conditional identity                           [#4054]
  -> nonnegative / real conditional integral identities     [#4057, #4060]
  -> conditional-expectation identification                 [#4066]
  -> regular conditional distribution / condExpKernel       [#4070]
  -> conditional-variance transport                         [#4077]
                                                               [INTEGRATED]

H. C5 RAW-DOOB FACTORIZATION

q_A = local x one-slab kernel
  -> normalize q_A against compact Haar to obtain nu_A
  -> literal C5 reference fiber weight = Omega_cont x q_A
  -> successive normalized Doob tilts compose exactly
  -> C5 reference fiber = Doob_{Omega_cont}(nu_A)            [#4080]
                                                               [INTEGRATED]

I. PRESENT FRONTIER

exact RCD + conditional variance + raw-Doob factorization
  -> quantitative remote conditional-law comparison         [OPEN NOW]
  -> distance-sensitive / summable covariance or influence  [OPEN NOW]
  -> volume-independent same-color row bound                 [OPEN]
  -> one color-block coercivity                              [OPEN]
  -> six-right + six-left block coercivity                   [OPEN]
  -> quantitative E12 Poincare coefficient                  [OPEN]
  -> scale-independent kappa_* > 0                          [OPEN]
  -> physical transfer gap >= 3 kappa_*/4                   [ROUTING INTEGRATED]

J. THERMODYNAMIC / CONTINUUM BOUNDARY

uniform finite-volume physical gap
  -> thermodynamic / scaling-limit physical carrier         [OPEN]
  -> physical OS/Wightman spectral lower bound              [OPEN]
  -> sufficiently rich same-root 4D Yang--Mills field/state [OPEN]
  -> correct vacuum structure / nontriviality               [OPEN]
  -> Clay-level existence + mass gap                        [OPEN]
```

---

# 1. Authority and proof discipline

The repository uses the following authority order:

```text
1. exact canonical GitHub SHA on the theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

Operational rules used throughout the current program include:

```text
start from the exact canonical SHA
keep theorem changes additive / tighten-only
never weaken assumptions merely to make Lean elaborate
use RED -> diagnose first genuine error -> GREEN
never call queued/in_progress CI successful
forbid sorry / admit / new axiom / proof placeholders
merge with the exact expected head SHA
re-observe the canonical branch after merge
```

---

# 2. Finite Wilson and same-root continuum infrastructure

The finite root is the interacting periodic-even compact `SU(N)` Wilson model with normalized compact Haar as reference measure. Canonical infrastructure includes Wilson action and Gibbs law, reflection positivity, gauge covariance, spatial-slice and boundary `L²` carriers, one-slab kernels, normalized physical transfer operators, and ground-state geometry.

In parallel, the repository contains a same-root scalar continuum Osterwalder--Schrader route from finite Wilson pushforwards through a continuum scalar probability law, reflection positivity, Hilbert completion, a real strongly continuous contraction semigroup, a graph-closed self-adjoint Hamiltonian, and a normalized vacuum sector.

That scalar continuum process is a genuine same-root continuum observable construction. It is **not** yet the full four-dimensional continuum Yang--Mills gauge field/state required by the Clay problem.

---

# 3. Finite physical transfer and twelve-spatial routing

At fixed finite volume the authoritative branch contains the physical top/non-top decomposition, contraction and power decay, fixed-space characterization, coercivity, spectral confinement, resolvent estimates, Green machinery, and relative Poincare control.

The actual ground-state one-slab joint law carries six right and six left genuine spatial conditional expectations. The already-formalized implication route is

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> raw physical one-slab defect coercivity
  -> physical transfer gap >= 3 kappa / 4.
```

This is an implication theorem. The missing object is still a model-derived coefficient that remains positive uniformly in the relevant volume/scale limit.

---

# 4. Sharp local one-link control and genuine `condExpL2`

PRs #3894, #3898, and #3907 prove a volume-independent one-link Harnack / normalized comparison / variance chain with the sharp local coefficient

```text
exp(-16 * beta).
```

PR #3909 transports the normalized direct law to the actual ground-state split fiber almost everywhere. PRs #3921--#3952 then integrate that information into the genuine joint `condExpL2` residual on an explicit dense bounded concrete core and dominate each one-link residual by the genuine spatial-color residual containing that link.

The repository does not promote arbitrary `L²` equivalence-class representatives to pointwise-defined fiber sections. Density and Hilbert-space closure are kept separate from pointwise measure statements.

---

# 5. Why naive same-color summation fails

PRs #3954, #3959, and #3964 produce a quantitative single-source remote comparison. PR #3969 then proves that assigning the same nonzero bound to every distinct same-color remote source gives a row majorant proportional to the number of remote links.

Therefore a constant pairwise Harnack estimate cannot by itself give volume-independent Dobrushin contraction. The missing ingredient must encode genuine locality, cancellation, or decay with source-target separation.

---

# 6. Remote dependence has been localized to covariance

The exact same-color raw Wilson analysis shows that the target-local raw factor cancels under a distinct same-color source change (#3978). The remaining physical dependence appears only after integration against the continuous physical vacuum.

PRs #3983--#4004 progressively rewrite that dependence as a covariance between a target-local observable and a source-local observable. PRs #4011 and #4016 replace the arbitrary `L²` vacuum representative by a canonical pointwise positive continuous-vacuum representative, normalize the reference weight to a genuine probability law, and obtain the exact form

```text
physical remote defect
  = source scalar * Z^2 * Cov_nu_ref(target-local ratio, source-local ratio).
```

This identifies exactly where any future distance decay must live. It does not prove that decay.

---

# 7. Reference-law conditional specification is now formalized

The former open disintegration frontier is now crossed.

The canonical sequence is:

```text
#4019  literal positive normalized one-link fiber law
#4024  fiber partition = singleton marginal
#4027  exact normalized density + base-point invariance
#4030  marginal x fiber expectation = weighted marginal
#4035  full normalized reference-law Fubini compatibility
#4039  measurable full-space one-link heat-bath Markov kernel + stationarity
#4042  exact heat-bath idempotence
#4045  factor through the concrete off-fiber sigma algebra
#4048  proper off-fiber Markov kernel
#4054  setwise conditional identity
#4057  conditional identity for nonnegative measurable observables
#4060  conditional identity for integrable real observables
#4066  heat-bath integral is a conditional-expectation representative
#4070  off-fiber heat-bath kernel = Mathlib condExpKernel a.e.
#4077  transfer doobBestConstantSquaredResidual / evariance through that RCD
```

The phrase "RCD" is therefore now justified for this reference one-link kernel in the precise off-fiber sense proved by #4070. That statement must not be generalized to unrelated fibers or to the full Wilson single-link conditional law without a separate theorem.

---

# 8. PR #4080: exact C5 raw-Doob factorization

PR #4080 adds the bridge needed to expose the internal structure of the C5 reference fiber.

For a selected one-link fiber, write

```text
q_A(g) = local(A[fiber <- g]) * oneSlabKernel(A[fiber <- g], B[source <- k]).
```

Normalize `q_A` against compact Haar to obtain a raw probability law `nu_A`. The literal C5 reference weight is then exactly

```text
Omega_cont(A[fiber <- g]) * q_A(g).
```

The proof establishes the required nonzero / finite first normalization mass and proves exact composition of the two normalized Doob tilts. Hence

```text
C5 reference fiber
  = Doob_{Omega_cont along fiber}(nu_A).
```

This is the current exact factorization boundary. In particular:

```text
C5 raw one-slab law != full-4D Wilson singleLinkConditionalMeasure
```

unless and until a separate theorem proves such an identification.

---

# 9. Present mathematical frontier

The next proof unit should consume the now-complete conditional-law structure rather than rebuild it.

The target is a genuinely spatially informative estimate of the form

```text
remote source change
  -> quantitative change of the actual reference one-link RCD
  -> coefficient depending on geometric separation / summable structure
  -> same-color row sum bounded independently of volume.
```

The raw one-slab law exposes exact Wilson locality; the remaining continuous-vacuum Doob factor exposes the precise place where correlations enter. A successful bound must exploit that structure rather than reusing the constant `exp(16 * beta)` pairwise majorant that #3969 already proved insufficient.

Once a volume-independent same-color block estimate is obtained, the program returns to the already-formalized global route: color blocks -> twelve-spatial Poincare -> scale-independent `kappa_*` -> finite physical transfer gap.

---

# 10. What is still open

The repository currently does **not** prove:

- summable or distance-decaying reference-law remote influence;
- a volume-independent same-color Dobrushin row bound;
- a positive scale-independent twelve-block Poincare coefficient;
- a uniform finite-volume physical transfer gap derived from that coefficient;
- the required thermodynamic/scaling-limit physical carrier with inherited positive gap;
- the full four-dimensional continuum Yang--Mills field/state satisfying the complete Clay formulation;
- Clay-level existence and mass gap.

These are mathematical boundaries, not documentation gaps.

---

# 11. Reading order

For the current proof-development order and the exact open frontier, see [`ROADMAP.md`](ROADMAP.md).

For theorem authority, always inspect the exact HEAD of

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

before relying on a historical SHA recorded in prose.
