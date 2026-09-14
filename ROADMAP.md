# MGAP4D Roadmap

This roadmap records the current proof architecture and immediate theorem-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-14 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The fresh exact canonical theorem HEAD observed before this documentation refresh is

```text
b4e38957f0264f1ed24b42fd4a4722a4238d94a7
```

which is the merge of PR #4094,

```text
Localize two-tilt normalized source change as cross-ratio defect
```

with exact GREEN proof head and CI receipt

```text
head:
  7ce26ca96783e067862aac51db809f1d6042c1c6

PR Lean Fast Check #13807
workflow run 34806695310
completed / success
```

`main` is a public landing surface, not theorem authority. The authority order is exact canonical SHA -> Lean artifacts -> README/ROADMAP -> CI receipts -> history/memory.

> **Current frontier**
>
> The reference-law RCD/conditional-variance route is integrated. The literal C5 reference fiber has been factored as `Omega_cont × local × source-sensitive one-slab kernel`, with the raw C5 law kept distinct from the full-4D Wilson `singleLinkConditionalMeasure`. PRs #4094/#4095 now provide a quotient-free two-source normalized-change interface that retains both source kernels and both exact partition functions.
>
> The next theorem unit is to expose `K_{k1} - K_{k2}` algebraically, before estimating it. Only after that exact carrier is available should target-source geometry be inserted. No exponential decay assumption is permitted unless it is actually derived on the present carrier.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated on bounded core** — canonical on the explicit dense bounded concrete core only.
- **Integrated routing** — implication chain is formalized but a quantitative model input is missing.
- **Obstruction integrated** — a rigorous negative theorem closes a tempting route.
- **Open now** — immediate constructive frontier.
- **Open next** — next coherent unit after the present carrier.
- **Open downstream** — required later in the global mass-gap route.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT                                                [Integrated]

periodic-even compact SU(N) Wilson model
  -> OS/reflection geometry
  -> spatial-slice and boundary L2 carriers
  -> physical one-slab transfer / ground-state structure

B. SAME-ROOT SCALAR CONTINUUM OS                                    [Integrated]

finite Wilson scalar readout
  -> continuum scalar law / OS positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> self-adjoint Hamiltonian / vacuum sector

C. FINITE GROUND-STATE CONDITIONAL DYNAMICS                         [Integrated routing]

ground-state one-slab joint law
  -> six right + six left genuine spatial condExp projections
  -> twelve-spatial family
  -> E12 -> E6 -> raw physical defect -> transfer-gap route

D. SHARP ONE-LINK CONTROL                                           [Integrated]

complete continuous-vacuum one-link weight
  -> pairwise Harnack
  -> sharp normalized comparison
  -> exp(-16 beta) variance lower bound
  -> genuine joint condExpL2 residual on bounded core

E. REMOTE CONSTANT-BOUND OBSTRUCTION                                [Obstruction integrated]

single-source comparison
  -> bounded-test influence
  -> constant same-color row majorant
  -> remote-link cardinality loss

F. LOCALITY / COVARIANCE LOCALIZATION                               [Integrated]

raw same-color Wilson cancellation
  -> source dependence localized
  -> four-integral defect = weighted covariance numerator
  -> target-local x source-local covariance interface

G. REFERENCE ONE-LINK CONDITIONAL LAW / RCD                         [Integrated]

literal normalized fiber
  -> Fubini / heat-bath kernel / stationarity / idempotence
  -> off-fiber factorization / properness
  -> conditional identities / conditional expectation
  -> condExpKernel / RCD
  -> conditional-variance transport

H. C5 RAW-DOOB FACTORIZATION                                        [Integrated]

q_A = local x one-slab kernel
  -> normalize q_A
  -> literal C5 weight = Omega_cont x q_A
  -> C5 reference fiber = Doob_{Omega_cont}(nu_A)

I. TWO-SOURCE CROSS-RATIO INTERFACE                                 [#4094/#4095 Integrated]

w(g) = Omega_cont x local
K_j(g) = K_slab(A[fiber <- g], B[source <- k_j])
Z_j = integral w K_j
I_j = integral w f K_j

Z_1 Z_2 (E_1 f - E_2 f) = I_1 Z_2 - I_2 Z_1

J. SOURCE-KERNEL DIFFERENCE                                         [Open now]

I_1 Z_2 - I_2 Z_1
  -> exact one-variable expression using K_1 - K_2
  -> retain target, source, k_1, k_2 explicitly
  -> no ratio K_1/K_2
  -> no distance estimate yet

K. GEOMETRIC SOURCE INFLUENCE                                       [Open next]

K_1 - K_2
  -> identify exact plaquette/support/incidence path
  -> identify which existing locality/distance APIs apply to this carrier
  -> prove finite-range, cancellation, distance-sensitive, or other summable variation
  -> do not assume C exp(-m d) without derivation

L. VOLUME-UNIFORM SAME-COLOR MIXING                                 [Open next]

source-sensitive coefficient c(target,source)
  -> sup_target sum_source c(target,source) < 1
  -> one same-color block coercivity

M. GLOBAL FINITE-VOLUME COERCIVITY                                  [Open / routing integrated]

six right + six left blocks
  -> quantitative E12 Poincare coefficient
  -> scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4

N. THERMODYNAMIC / CONTINUUM PROPAGATION                            [Open downstream]

uniform finite-volume physical gap
  -> thermodynamic/scaling-limit carrier
  -> physical OS/Wightman spectral lower bound
  -> full same-root 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules:

```text
start from the fresh exact authoritative SHA
use GitHub-mediated repository operations
accept CI only when workflow, job, and Lean step are terminal success
inspect the first genuine terminal Lean failure before editing
keep theorem development additive / tighten-only
never weaken or invent assumptions merely to make elaboration pass
forbid sorry / admit / new axiom / proof placeholders
merge against the exact expected work-head
re-observe the authoritative branch after merge
```

Permanent claim boundaries:

```text
finite theorem != continuum theorem
positive coefficient at each scale != uniform positive coefficient
local Harnack / variance != global L2 Poincare
bounded-core theorem != arbitrary-L2 pointwise theorem
covariance localization != covariance decay
RCD identification != quantitative mixing
C5 raw one-slab law != full-4D Wilson singleLinkConditionalMeasure
uniform pairwise remote bound != summable row bound
CI success != theorem authority
same-root scalar continuum != full 4D Yang--Mills field
intermediate formal theorem != Clay-level mass-gap theorem
```

---

# Phase 1 — Finite Wilson root

**Status: Integrated.**

The finite root contains the interacting periodic-even compact `SU(N)` Wilson Gibbs model, normalized compact Haar reference measure, lattice/plaquette geometry, Wilson action, reflection positivity, gauge covariance, spatial-slice carriers, one-slab kernels, normalized physical transfer operators, and positive ground-state structure.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The canonical route constructs a continuum scalar law from finite Wilson readouts, establishes continuum reflection positivity, forms the OS Hilbert carrier, obtains a real strongly continuous contraction semigroup and self-adjoint Hamiltonian, and identifies a normalized vacuum sector.

Boundary: this is not yet the complete four-dimensional Yang--Mills gauge field/state.

---

# Phase 3 — Finite physical transfer and twelve-spatial routing

**Status: Integrated routing.**

At fixed volume the theorem tree contains the physical top/non-top decomposition, contraction/coercivity/resolvent/Green machinery, the actual six-right and six-left ground-state spatial conditional expectations, and the implication route

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

Open quantitative input: a model-derived coefficient with the required uniform scale behavior.

---

# Phase 4 — Sharp one-link control

**Status: Integrated.**

The continuous-vacuum one-link law has a volume-independent Harnack/normalized-comparison/variance chain. The variance scale `exp(-16 * beta)` is available and has been transported into the genuine joint conditional-residual setting on the explicit bounded core.

This is local control; it is not a global same-color contraction theorem.

---

# Phase 5 — Constant remote influence is insufficient

**Status: Obstruction integrated through #3969.**

A uniform single-source remote comparison exists, but assigning the same nonzero coefficient to every distinct same-color source produces a row majorant proportional to the number of remote sources.

Completion criterion: satisfied as a negative theorem. The constant-row-majorant route is closed.

---

# Phase 6 — Localize the true remote dependence

**Status: Integrated.**

Raw same-color Wilson locality removes the irrelevant remote factor. The remaining source dependence after continuous-vacuum integration has been localized into covariance/cross-ratio expressions with target-local and source-local structure kept visible.

Completion criterion: exact localization, not decay.

---

# Phase 7 — Exact reference one-link conditional law

**Status: Integrated through the RCD and conditional-variance layer.**

The completed ladder is

```text
literal positive normalized fiber
  -> singleton marginal / exact density
  -> local normalization and full-law Fubini
  -> measurable heat-bath kernel / stationarity / idempotence
  -> off-fiber factorization / properness
  -> setwise and integral conditional identities
  -> conditional-expectation representative
  -> a.e. condExpKernel / RCD identification
  -> conditional-variance transport.
```

Do not reopen this phase unless a later carrier exposes a genuinely missing hypothesis.

---

# Phase 8 — C5 reference fiber as continuous-vacuum Doob tilt

**Status: Integrated.**

For a selected target fiber,

```text
q_A(g)
  = local(A[fiber <- g])
    * oneSlabKernel(A[fiber <- g], B[source <- k]).
```

Normalize `q_A` against compact Haar to obtain `nu_A`. The literal reference-fiber weight is

```text
Omega_cont(A[fiber <- g]) * q_A(g),
```

and the normalized reference fiber is the corresponding continuous-vacuum Doob tilt.

Permanent boundary:

```text
nu_A is the normalized raw C5 one-slab law.
It is not the full-4D Wilson singleLinkConditionalMeasure by definition.
```

---

# Phase 9 — Quotient-free two-source normalized change

**Status: Integrated by #4094/#4095.**

Keep the common target weight and the two source kernels separate:

```text
w(g)   = Omega_cont(A[fiber <- g]) * local(A[fiber <- g])
K_j(g) = oneSlabKernel(A[fiber <- g], B[source <- k_j]).
```

Then

```text
Z_j = integral w(g) K_j(g) dg
I_j = integral w(g) f(g) K_j(g) dg
```

and the normalized source change satisfies

```text
Z_1 Z_2 (E_1 f - E_2 f)
  = I_1 Z_2 - I_2 Z_1.
```

No likelihood-ratio quotient is needed. This is the preferred surface for retaining geometric source information.

---

# Phase 10 — Expose the source-kernel difference

**Status: Open now.**

The next theorem carrier should be algebraic and quotient-free. A preferred one-variable normal form is

```text
I_1 Z_2 - I_2 Z_1
  = (I_1 - I_2) Z_2 - I_2 (Z_1 - Z_2)
```

with

```text
I_1 - I_2 = integral w(g) f(g) (K_1(g) - K_2(g)) dg
Z_1 - Z_2 = integral w(g)       (K_1(g) - K_2(g)) dg.
```

This carrier is preferred before a two-variable antisymmetrization because it does not introduce Fubini/product-integrability obligations solely for presentation.

Completion criterion:

```text
the source values k_1,k_2 occur only through an explicit K_1-K_2 term,
while target/source/fiber parameters remain visible.
```

No geometric estimate is part of this phase.

---

# Phase 11 — Identify exact geometric support of `K_1-K_2`

**Status: Open next.**

Canonical inspection must determine how the update

```text
B -> Function.update B source k
```

changes the one-slab kernel. The kernel consists of the left spatial half-weight, the temporal crossing product, and the right spatial half-weight. Existing target-local factorization, touching-plaquette, same-color locality, finite-lattice incidence, and distance APIs are candidates, but each must be matched to the exact compact `SU(N)` C5 carrier.

The objective is an exact statement of which local factors can differ, not yet an asymptotic estimate.

---

# Phase 12 — Derive summable source variation

**Status: Open next.**

From the exact support statement, derive a coefficient `c(target,source)` that is summable over same-color sources. Possible valid mechanisms include finite interaction range, exact cancellation, or a genuinely proved distance-decay estimate.

Forbidden shortcut:

```text
assume c(target,source) <= C * exp(-m * d(target,source))
```

without a theorem deriving that estimate on the present carrier.

Completion criterion:

```text
sup_target sum_source c(target,source) < 1
```

or another formally sufficient, volume-independent block-coercivity criterion derived from the actual model.

---

# Phase 13 — Same-color and twelve-spatial coercivity

**Status: Open after Phase 12.**

A summable source estimate should feed the existing one-link variance/control machinery to obtain one same-color block coercivity, then all six right and six left blocks, and finally a quantitative twelve-spatial Poincare coefficient.

---

# Phase 14 — Uniform finite-volume physical gap

**Status: Open downstream; routing already integrated.**

The required input is a scale-independent positive lower bound

```text
exists kappa_* > 0,
  kappa_* <= kappa(H,N,beta)
```

on the relevant sequence of volumes/scales. The existing routing then yields

```text
physical transfer gap >= 3 * kappa_* / 4.
```

---

# Phase 15 — Thermodynamic / continuum propagation

**Status: Open downstream.**

A uniform finite-volume gap must still be transported to the appropriate thermodynamic/scaling-limit physical carrier, then connected to the physical OS/Wightman spectral statement and a sufficiently rich same-root four-dimensional Yang--Mills field/state.

---

# Phase 16 — Clay-level completion

**Status: Open.**

The final program must still establish the complete continuum Yang--Mills existence statement, the correct vacuum/nontriviality structure, and a strictly positive physical spectral gap above the vacuum in the sense required by the Clay problem.

These are mathematical boundaries, not documentation gaps.
