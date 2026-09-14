# MGAP4D Roadmap

This roadmap records the current proof architecture and immediate theorem-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-14 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The fresh exact mathematical theorem baseline observed before this documentation refresh is

```text
ad38daddab638cfc45ac47edd796505527291e78
```

which is the merge of PR #4103,

```text
Factor distinct C5 source change as a scalar
```

with exact GREEN proof head and CI receipt

```text
head:
  c66fd63a13b28365e87ca0dcbc9f8f4afd698d67

PR Lean Fast Check #13811
workflow run 34809368834
completed / success
```

`main` is a public landing surface, not theorem authority. The authority order is exact canonical SHA -> Lean artifacts -> README/ROADMAP -> CI receipts -> history/memory.

A docs-only merge may advance the current branch pointer beyond the theorem baseline above. Such a documentation commit does not by itself change the mathematical theorem frontier.

> **Current frontier**
>
> The reference-law RCD/conditional-variance route is integrated. The literal C5 reference fiber is factored as `Omega_cont × local × source-sensitive one-slab kernel`, while the C5 raw law remains explicitly distinct from the full-4D Wilson `singleLinkConditionalMeasure`.
>
> PR #4101 exposed the literal source-kernel difference `K_1-K_2` inside the quotient-free normalized-change identity. PR #4103 then proved that, when `source != fiber`, this difference is a fiber-independent scalar difference times one common base one-slab kernel.
>
> The next theorem unit is therefore **normalized scalar cancellation**, not an assumed distance-decay estimate. The immediate goal is to prove that the individual positive source multiplier cancels from the normalized literal C5 fiber probability law. Only after that theorem is established should the exact result be bridged back to same-color influence and block coercivity.

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

E. CONSTANT REMOTE-BOUND OBSTRUCTION                                [Obstruction integrated]

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

J. SOURCE-KERNEL DIFFERENCE                                         [#4101 Integrated]

I_1 Z_2 - I_2 Z_1
  -> integral w f (K_1-K_2)
  -> integral w   (K_1-K_2)
  -> no K_1/K_2 quotient

K. DISTINCT-SOURCE SCALAR FACTORIZATION                             [#4103 Integrated]

K_1(g)-K_2(g)
  -> source-local factor difference x common base kernel
  -> source != fiber makes source-local factors independent of g
  -> (c_1-c_2) x common base kernel

L. NORMALIZED SCALAR CANCELLATION                                   [Open now]

source != fiber
  -> individual positive scalar factorization W_k = c_k W_base
  -> Z_k = c_k Z_base
  -> normalized C5 fiber law independent of k
  -> exact distinct-source C5 invariance

M. C5-TO-SAME-COLOR BRIDGE                                          [Open next]

exact C5 distinct-source invariance, if proved
  -> identify the exact original conditional carrier it controls
  -> transport zero influence only where justified
  -> isolate any remaining incidence cases

N. VOLUME-UNIFORM SAME-COLOR COERCIVITY                             [Open next]

zero or summable source-sensitive coefficients
  -> one same-color block coercivity
  -> six right + six left blocks
  -> quantitative twelve-spatial Poincare coefficient

O. UNIFORM FINITE-VOLUME PHYSICAL GAP                               [Open / routing integrated]

scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4

P. THERMODYNAMIC / CONTINUUM PROPAGATION                            [Open downstream]

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
source-kernel scalar factorization != normalized law equality
normalized C5 law equality != automatic global same-color influence theorem
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

This obstruction remains important even after #4103: if a future carrier has genuinely nonzero long-range dependence, a uniform constant coefficient is still insufficient. What #4103 changes is that the present C5 distinct-source lane may admit exact cancellation before any such summation is needed.

---

# Phase 6 — Localize the true remote dependence

**Status: Integrated.**

Raw same-color Wilson locality removes irrelevant remote factors. The remaining source dependence after continuous-vacuum integration is localized into covariance/cross-ratio expressions with target-local and source-local structure kept visible.

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

For a selected fiber,

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

and

```text
Z_1 Z_2 (E_1 f - E_2 f)
  = I_1 Z_2 - I_2 Z_1.
```

No likelihood-ratio quotient is needed. This remains the preferred normalization surface.

---

# Phase 10 — Expose the source-kernel difference

**Status: Integrated by #4101.**

The previous open algebraic target is now closed.

PR #4101 proves generic and C5-specialized identities that rewrite

```text
I_1 Z_2 - I_2 Z_1
```

using the literal pointwise difference

```text
K_1(g) - K_2(g).
```

Schematically,

```text
I_1 Z_2 - I_2 Z_1
  = Z_2 * integral w f (K_1-K_2)
      - I_2 * integral w (K_1-K_2).
```

The added hypotheses are exactly the integrability assumptions needed for real-integral subtraction. No distance estimate or full-4D conditional-law identification is introduced.

Completion criterion: satisfied.

---

# Phase 11 — Factor the exact source update

**Status: Integrated by #4103.**

PR #4103 proves the exact one-slab source-update structure

```text
K_1(g)-K_2(g)
  = (L_source(k_1;g)-L_source(k_2;g)) * K_base(g),
```

where `L_source` is the exact right-boundary source-local Boltzmann factor and `K_base` is the one-slab kernel before the right source update.

It then proves that if

```text
source != fiber,
```

the source-local factor is independent of the selected fiber value `g`:

```text
L_source(k;g) = L_source(k).
```

Therefore

```text
K_1(g)-K_2(g)
  = (c_1-c_2) * K_base(g).
```

All fiber-variable dependence lies in the common base kernel.

Completion criterion: satisfied for this exact scalar-difference carrier.

---

# Phase 12 — Normalize away the distinct-source scalar

**Status: Open now.**

This is the immediate theorem-development unit.

The objective is to pass from the #4103 difference statement plus the existing individual source-update factorization to a pointwise weight factorization of the form

```text
W_k(g) = c_k * W_base(g)
```

for `source != fiber`, where

```text
c_k > 0
```

and `c_k` is independent of `g`.

Then prove

```text
Z_k = c_k * Z_base
```

and cancel the scalar in the normalized law:

```text
realIntegralWeightedProbabilityMeasure Haar W_k
  = realIntegralWeightedProbabilityMeasure Haar W_base.
```

A generic theorem for positive scalar rescaling of `realIntegralWeightedProbabilityMeasure` may be introduced if that is the cleanest exact interface.

Preferred assumptions:

- only the nonnegativity/integrability/mass-positivity required by the normalization API;
- positivity/nonvanishing of the scalar from the already formalized Boltzmann factor;
- no distance-decay assumption;
- no new global conditional-law identification.

Completion criterion:

```text
for source != fiber,
  literal normalized C5 fiber law with source value k_1
    =
  literal normalized C5 fiber law with source value k_2.
```

Until this equality is a Lean theorem, the roadmap treats it as an open target, not as an established consequence of #4103.

---

# Phase 13 — Convert normalized equality into exact zero source change

**Status: Open next.**

Once Phase 12 proves equality of the literal C5 fiber probability measures for distinct source/fiber indices, derive the most useful corollaries:

```text
E_{k_1}[f] - E_{k_2}[f] = 0
```

for every integrable/bounded observable on the relevant fiber, and corresponding zero influence statements on the exact C5 carrier.

Prefer measure equality as the primary theorem and expectation-zero results as corollaries, because measure equality is stronger and avoids duplicating observable-specific assumptions.

---

# Phase 14 — Bridge exact C5 invariance back to same-color dynamics

**Status: Open next.**

This is a separate theorem phase. Do not collapse it into Phase 12.

The exact questions are:

```text
1. Which original same-color conditional-law carrier is represented by the C5 fiber law?
2. Under what hypotheses is a distinct same-color source mapped to source != fiber in the C5 coordinates?
3. Does the existing RCD / raw-Doob / ground-state bridge transport the exact measure equality directly?
4. Are there any source-incidence cases left where source = fiber or another local interaction survives?
```

Completion criterion: an explicit theorem transporting C5 distinct-source invariance to the actual coefficient used in the same-color/block-coercivity route.

Forbidden shortcut:

```text
C5 normalized equality
  => all full-4D remote coefficients are zero
```

without the formal carrier-identification theorem.

---

# Phase 15 — Decide whether any summable nonzero remainder remains

**Status: Open after Phase 14.**

There are now two logically possible outcomes.

**Route A — exact locality/cancellation closes the remote part.**

If the bridge proves that every distinct same-color remote source falls under the exact C5 invariance theorem, the corresponding off-diagonal influence coefficients may be exactly zero. Then no distance-decay theorem is needed for that part of the block argument.

**Route B — a nonzero remainder survives.**

If some legitimate carrier retains nonzero dependence, derive a coefficient `c(target,source)` from the actual remaining interaction. Valid mechanisms include finite interaction range, exact incidence bounds, or a genuinely proved distance-sensitive estimate.

The old forbidden shortcut remains forbidden:

```text
assume c(target,source) <= C * exp(-m * d(target,source))
```

without deriving it on the present carrier.

Completion criterion for any nonzero remainder:

```text
sup_target sum_source c(target,source) < 1
```

or another formally sufficient volume-independent block-coercivity criterion.

---

# Phase 16 — Same-color and twelve-spatial coercivity

**Status: Open after the C5-to-same-color bridge.**

Use exact zero remote influence and/or the remaining summable source estimate together with the existing one-link variance/control machinery to obtain one same-color block coercivity, then all six right and six left blocks, and finally a quantitative twelve-spatial Poincare coefficient.

The repository should prefer the strongest exact input available:

```text
zero coefficient > finite-range coefficient > proved decay coefficient > uniform constant bound.
```

The last option alone is already known to lose volume uniformity.

---

# Phase 17 — Uniform finite-volume physical gap

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

# Phase 18 — Thermodynamic / continuum propagation

**Status: Open downstream.**

A uniform finite-volume gap must still be transported to the appropriate thermodynamic/scaling-limit physical carrier, then connected to the physical OS/Wightman spectral statement and a sufficiently rich same-root four-dimensional Yang--Mills field/state.

---

# Phase 19 — Clay-level completion

**Status: Open.**

The final program must still establish the complete continuum Yang--Mills existence statement, the correct vacuum/nontriviality structure, and a strictly positive physical spectral gap above the vacuum in the sense required by the Clay problem.

These are mathematical boundaries, not documentation gaps.
