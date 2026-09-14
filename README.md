# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional expectations, quantitative mixing, and the mass-gap problem.

The repository is deliberately conservative about claims. It separates exact finite-volume theorems, almost-everywhere bridges, conditional-law identifications, quantitative coercivity inputs, continuum reconstruction, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current theorem frontier is finite-volume and quantitative. The exact reference one-link conditional law, its off-fiber RCD realization, its conditional-variance transport, and the C5 continuous-vacuum / local / one-slab-kernel factorization are formalized. The newest two-source interface keeps the two source-dependent one-slab kernels separate and removes normalization denominators without introducing a source-kernel quotient.
>
> What is **not** yet proved is the distance-sensitive or otherwise summable remote-influence estimate needed to turn those exact identities into volume-uniform same-color block coercivity.

---

## Repository authority — 2026-09-14 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Fresh exact canonical HEAD observed before this documentation refresh:
  b4e38957f0264f1ed24b42fd4a4722a4238d94a7

That commit is the merge of:
  PR #4094
  Localize two-tilt normalized source change as cross-ratio defect

Exact GREEN proof head for #4094:
  7ce26ca96783e067862aac51db809f1d6042c1c6

Validation receipt:
  PR Lean Fast Check #13807
  workflow run 34806695310
  completed / success

Public landing branch:
  main
```

The authority order is fixed:

```text
1. exact canonical GitHub SHA on the theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public landing surface, not theorem authority when histories differ. A CI receipt establishes that a particular tree was checked successfully; it is operational evidence, not a substitute for the theorem statement or the exact canonical source tree.

---

# Current theorem architecture

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> spatial-slice and boundary L2 carriers
  -> physical one-slab transfer and ground-state structure
                                                               [INTEGRATED]

B. SAME-ROOT SCALAR CONTINUUM OS LANE

finite Wilson scalar readout
  -> continuum scalar probability law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> self-adjoint OS Hamiltonian / vacuum sector
                                                               [INTEGRATED]

C. FINITE PHYSICAL / GROUND-STATE CONDITIONAL LANE

ground-state one-slab joint probability law
  -> six right + six left genuine spatial condExp projections
  -> twelve-spatial family
  -> E12 -> E6 -> raw physical defect -> transfer-gap routing
                                                               [INTEGRATED ROUTING]

D. SHARP ONE-LINK CONTROL

continuous-vacuum complete one-link weight
  -> exp(16 beta) pairwise Harnack
  -> sharp normalized Haar comparison
  -> exp(-16 beta) one-link variance lower bound
  -> genuine joint condExpL2 residual on bounded core
                                                               [INTEGRATED]

E. REMOTE-INFLUENCE OBSTRUCTION

single-source remote comparison
  -> bounded-test influence
  -> naive constant same-color row majorant
  -> link-count / volume loss
                                                               [OBSTRUCTION INTEGRATED]

F. LOCALITY / COVARIANCE LOCALIZATION

raw same-color Wilson cancellation
  -> source dependence localized
  -> four-integral defect = weighted covariance numerator
  -> target-local x source-local covariance interface
                                                               [INTEGRATED]

G. EXACT REFERENCE ONE-LINK CONDITIONAL LAW

literal normalized one-link fibers
  -> Fubini compatibility
  -> measurable heat-bath kernel / stationarity / idempotence
  -> off-fiber factorization and properness
  -> setwise and integral conditional identities
  -> conditional expectation
  -> condExpKernel / RCD identification
  -> conditional-variance transport
                                                               [INTEGRATED]

H. C5 REFERENCE-FIBER FACTORIZATION

q_A(g) = local(A[fiber <- g]) * K_slab(A[fiber <- g], B[source <- k])
  -> normalize q_A against compact Haar
  -> literal C5 weight = Omega_cont(A[fiber <- g]) * q_A(g)
  -> C5 reference fiber = continuous-vacuum Doob tilt of raw q_A law
                                                               [INTEGRATED]

I. TWO-SOURCE QUOTIENT-FREE INTERFACE

common target weight
  w(g) = Omega_cont(A[fiber <- g]) * local(A[fiber <- g])

source kernels
  K_k(g) = K_slab(A[fiber <- g], B[source <- k])

partition / observable integrals
  Z_j = integral w(g) K_{k_j}(g) dg
  I_j = integral w(g) f(g) K_{k_j}(g) dg

normalized source change
  Z_1 Z_2 (E_1 f - E_2 f)
    = I_1 Z_2 - I_2 Z_1
                                                               [#4094 / #4095 INTEGRATED]

J. PRESENT FRONTIER

two-source cross-ratio defect
  -> expose K_{k_1} - K_{k_2} without quotient
  -> identify exact combinatorial/geometric support of source influence
  -> derive distance-sensitive or otherwise summable kernel variation
  -> volume-uniform same-color row bound
                                                               [OPEN]

K. DOWNSTREAM GAP ROUTE

one same-color block coercivity
  -> six right + six left blocks
  -> quantitative E12 Poincare coefficient
  -> scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4
                                                               [ROUTING PARTLY INTEGRATED]

L. THERMODYNAMIC / CONTINUUM COMPLETION

uniform finite-volume physical gap
  -> thermodynamic / scaling-limit physical carrier
  -> physical OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                               [OPEN]
```

---

# 1. Exact conditional-law / reference-fiber route

The reference-law disintegration problem is no longer the immediate bottleneck. The canonical theorem chain constructs the literal normalized one-link fiber, proves the required Fubini and conditional identities, builds the measurable heat-bath kernel, factors it through the off-fiber sigma algebra, proves properness, identifies its integral with conditional expectation, identifies the kernel almost everywhere with Mathlib's `condExpKernel`, and transports the relevant conditional variance.

Accordingly, later quantitative arguments may use the proved reference RCD interface. They must not silently generalize it to unrelated fibers or to the full Wilson single-link conditional law.

---

# 2. The C5 raw / continuous-vacuum split

For a selected C5 target fiber, the exact source-dependent raw factor is kept as

```text
local x one-slab kernel.
```

The continuous-vacuum factor is separate:

```text
nu_A
  -- Omega_cont Doob tilt -->
mu_ref,A,fiber.
```

Equivalently, the literal C5 fiber weight has the pointwise form

```text
Omega_cont x local x kernel.
```

This distinction is permanent unless a later theorem proves more. In particular,

```text
C5 raw one-slab law != full-4D Wilson singleLinkConditionalMeasure
```

by naming or definition alone.

---

# 3. Why the two-source interface matters

PRs #4094 and #4095 preserve the target link, source link, the two source values, the two source-dependent one-slab kernels, and both exact partition functions. They cross-multiply the normalized expectations before any ratio `K_{k_1}/K_{k_2}` is introduced.

The resulting identity is

```text
Z_1 Z_2 (E_1 f - E_2 f) = I_1 Z_2 - I_2 Z_1.
```

This is the correct algebraic surface for the next localization step because source dependence remains visible. The next carrier should rewrite the right-hand side in terms of `K_{k_1} - K_{k_2}` (or an equivalent antisymmetric two-kernel defect) before any geometric estimate is imposed.

---

# 4. What the global Harnack bound does and does not do

The volume-independent local Harnack machinery remains useful. In particular, the existing comparison scale based on `exp(8 * beta)` and the corresponding variance scale `exp(-16 * beta)` provide robust local positivity/comparison control.

They do **not** by themselves encode target-source separation. Summing the same nonzero remote coefficient over every same-color source produces a row bound proportional to the number of sources. That obstruction is already formalized.

Therefore the present problem is not to derive another global constant. It is to preserve geometry long enough to prove a coefficient that is summable in the source variable.

---

# 5. Present mathematical frontier

The immediate target is an exact chain of the form

```text
I_1 Z_2 - I_2 Z_1
  -> source-kernel difference K_{k_1} - K_{k_2}
  -> exact locality / support / incidence statement
  -> quantitative kernel variation retaining target-source separation
  -> summable same-color influence coefficient
  -> sup_target sum_source c(target,source) < 1
```

The repository contains finite-lattice locality, plaquette-incidence, and several distance/covariance constructions in other lanes. Those results may only be reused after their hypotheses and carriers are matched to the present compact `SU(N)` C5 one-slab setting. No estimate of the form

```text
C * exp(-m * d(target,source))
```

is assumed merely because it is the desired endpoint.

---

# 6. Formalized / unproved boundary

Currently formalized on the authoritative theorem carrier include:

- exact finite Wilson and physical-transfer infrastructure;
- the reference one-link RCD / `condExpKernel` route;
- sharp local one-link Harnack and variance comparison;
- raw same-color locality and the link-count obstruction for a constant remote bound;
- covariance / cross-ratio localization;
- the exact `Omega_cont x local x one-slab-kernel` C5 reference-fiber structure;
- quotient-free two-source normalized-change identities retaining both kernels.

Not yet formalized as a theorem sufficient for the mass-gap route are:

- a target-source-distance-sensitive C5 source-kernel variation bound;
- a summable same-color remote influence coefficient;
- a volume-independent same-color Dobrushin/block-coercivity bound;
- a scale-independent positive twelve-block Poincare coefficient derived from the model;
- a uniform finite-volume physical transfer gap obtained from that coefficient;
- the required thermodynamic/scaling-limit physical carrier with inherited positive gap;
- the full four-dimensional continuum Yang--Mills field/state required by the Clay formulation;
- Clay-level existence and mass gap.

---

# 7. Proof discipline

Repository development follows these rules:

```text
start from the fresh exact canonical theorem-carrier SHA
keep theorem changes additive / tighten-only
separate observed facts from intended estimates
never manufacture a decay theorem to close a downstream goal
use RED -> diagnose the first genuine Lean failure -> GREEN
never call queued or in-progress CI successful
forbid sorry / admit / new axiom / proof placeholders
merge only against the exact expected work-head
re-observe the authoritative branch after every merge
```

For the ordered next steps, see [`ROADMAP.md`](ROADMAP.md).
