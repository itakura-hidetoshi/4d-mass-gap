# MGAP4D Roadmap

This roadmap records the current proof architecture and immediate theorem-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-15 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest mathematical theorem baseline before this documentation refresh is

```text
b7bf4dc6e590f88c64e5a01d018da60155e8ace5
```

which is the merge of PR #4177,

```text
Lift C5 stationary average to sweep exponential residual
```

with exact final GREEN head and CI receipt

```text
head:
  68fbb3385b7e3470ed7bb041c7e86efab69da286

PR Lean Fast Check #13887
workflow run 34908048470
workflow / job / changed-Lean step: completed / success
```

Tree at that theorem baseline:

```text
8c7cb7aade0be712df53702613f5b9fade64c699
```

`main` is a public landing surface, not theorem authority. The authority order is exact canonical SHA -> Lean artifacts -> README/ROADMAP -> CI receipts -> history/memory.

A docs-only merge may advance the current branch pointer beyond the theorem baseline above without changing the latest mathematical theorem-bearing result.

> **Current frontier**
>
> The old normalized-scalar-cancellation frontier is closed. Distinct right-boundary source values now give literally equal normalized C5 fiber probability measures whenever `source != fiber`; the equality propagates to the conditional and heat-bath carriers, so the corresponding real-test influence is exactly zero.
>
> The remaining C5 cross-boundary influence is supported only on `source = fiber`. The whole source row therefore equals the single coefficient `q(beta)` with no volume factor. For `beta < log 3 / 16`, `q(beta) < 1`.
>
> This proved influence has been packaged as a one-way tagged carrier on `Sum Link Link`, propagated through reciprocal random-scan response bounds, and lifted to stationary comparison. The source resolvent has exact cardinality cancellation, source averaging removes the explicit terminal cardinality, and full-sweep time gives the volume-independent residual `exp(-(1-q(beta))*sweeps)`.
>
> The immediate open problem is now to **close the normalized stationary source term and the genuine comparison-data bridge** needed to connect the C5 carrier to the existing spatial Poincare/coercivity route. #4177 is still a conditional comparison theorem, not yet the desired physical coercivity theorem.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated on bounded core** — canonical on the explicit dense bounded concrete core only.
- **Integrated routing** — implication chain is formalized but a quantitative model input is missing.
- **Integrated conditional interface** — the theorem is proved, but application requires genuine comparison/model data supplied separately.
- **Obstruction integrated** — a rigorous negative theorem closes a tempting route.
- **Open now** — immediate constructive frontier.
- **Open next** — next coherent unit after the present frontier.
- **Open downstream** — required later in the global mass-gap route.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT                                                [Integrated]

periodic-even compact SU(N) Wilson model
  -> OS/reflection geometry
  -> spatial-slice / boundary L2 carriers
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

uniform nonzero remote coefficient
  -> remote-link cardinality loss
  -> cannot yield volume-independent row contraction by itself

F. LOCALITY / RCD / C5 FACTORIZATION                                [Integrated]

raw same-color locality
  -> covariance / cross-ratio localization
  -> literal normalized one-link fiber
  -> heat-bath / off-fiber RCD / conditional variance
  -> C5 raw-Doob factorization
  -> explicit source-kernel difference
  -> distinct-source scalar factorization

G. NORMALIZED DISTINCT-SOURCE INVARIANCE                            [Integrated]

source != fiber
  -> W_k = c_k W_base
  -> Z_k = c_k Z_base
  -> normalized C5 fiber law independent of k
  -> conditional-kernel equality
  -> heat-bath-kernel equality
  -> exact zero real-test influence

H. CROSS-BOUNDARY SUPPORT / ROW SUM                                 [Integrated]

off diagonal: 0
source = fiber: diagonal Harnack coefficient
  -> row support is one coordinate
  -> rowSum = q(beta)
  -> beta < log 3 / 16 => q(beta) < 1

I. ONE-WAY TAGGED CARRIER                                           [Integrated]

ι_H = Sum Link Link
right-source -> left-target block = proved C5 influence
other blocks = carrier-scope zero
  -> volume-independent row certificate
  -> volume-independent column certificate

J. RECIPROCAL RANDOM-SCAN RESPONSE                                  [Integrated]

r_{H,beta} = reciprocal one-coordinate rate
1-r = (1-q)/card(ι_H)
  -> n-step variation <= r^n * magnitude
  -> one-coordinate rate itself is not volume-uniform

K. STATIONARY COMPARISON / SOURCE RESOLVENT                         [Integrated conditional interface]

genuine finite positive-weight stationary non-strict comparison
+ entrywise C5 domination
  -> kernel residual comparison
  -> exact card/resolvent cancellation
  -> source-summed discrepancy bound
  -> source-average normalization

L. SWEEP RESCALING                                                   [Integrated]

r_{H,beta}^{card(ι_H)*sweeps}
  <= exp(-(1-q(beta))*sweeps)

M. STATIONARY SWEEP-AVERAGE COMPARISON                              [#4177 Integrated conditional interface]

average expectation discrepancy
  <= normalized source resolvent
     + 2 exp(-(1-q(beta))*sweeps) * magnitude

N. CLOSE NORMALIZED SOURCE TERM                                     [Open now]

uniform normalized sourceEnvelope bound
+ genuine comparison-data realization
  -> fully volume-independent stationary comparison

O. PHYSICAL POINCARE / COERCIVITY BRIDGE                            [Open next]

stationary comparison output
  -> one same-color / relevant block coercivity
  -> six right + six left blocks
  -> quantitative twelve-spatial Poincare coefficient

P. UNIFORM FINITE-VOLUME PHYSICAL GAP                               [Open downstream / routing integrated]

scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4

Q. THERMODYNAMIC / CONTINUUM PROPAGATION                            [Open downstream]

uniform finite-volume physical gap
  -> thermodynamic/scaling-limit physical carrier
  -> physical OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state
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
C5 distinct-source invariance != arbitrary full-4D remote invariance
one-way tagged carrier zero block != reverse physical influence zero
Sum.inl link != Sum.inr link
q(beta) < 1 != volume-uniform one-coordinate random-scan rate
conditional stationary comparison != physical coercivity theorem
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

The continuous-vacuum one-link law has a volume-independent Harnack/normalized-comparison/variance chain. The one-link variance scale `exp(-16 * beta)` is available and has been transported into the genuine joint conditional-residual setting on the explicit bounded core.

This is local control; it is not by itself a global block contraction theorem.

---

# Phase 5 — Constant remote influence obstruction

**Status: Obstruction integrated through #3969.**

A nonzero constant pairwise remote coefficient summed over every source carries an explicit remote-link cardinality factor. This route cannot establish volume-independent same-color contraction.

The result remains important as a permanent warning: if a later physical carrier retains genuine nonzero long-range dependence, a constant remote bound is still insufficient.

---

# Phase 6 — Exact reference conditional law and C5 source structure

**Status: Integrated.**

The completed infrastructure includes:

```text
literal normalized one-link fiber
  -> full-law Fubini compatibility
  -> measurable heat-bath kernel / stationarity / idempotence
  -> off-fiber factorization / properness
  -> conditional expectation
  -> condExpKernel / RCD identification
  -> conditional-variance transport
  -> C5 raw-Doob factorization
  -> quotient-free two-source cross-ratio
  -> explicit source-kernel difference
  -> distinct-source scalar factorization.
```

The permanent boundary remains:

```text
C5 raw one-slab law != full-4D Wilson singleLinkConditionalMeasure
```

unless a separate theorem proves such an identification.

---

# Phase 7 — Normalize away the distinct-source scalar

**Status: Integrated.**

This was the previous open frontier and is now closed.

For `source != fiber`, the theorem chain proves

```text
W_k(g) = c_k * W_base(g),
```

where `c_k > 0` is independent of the fiber integration variable. The partition function scales by the same scalar, so

```text
realIntegralWeightedProbabilityMeasure Haar W_{k1}
  = realIntegralWeightedProbabilityMeasure Haar W_{k2}.
```

This equality is at the normalized measure level.

---

# Phase 8 — Propagate invariance to the conditional carrier

**Status: Integrated.**

The normalized measure equality gives pointwise equality of the C5 one-link conditional kernels for distinct source/fiber coordinates. The equality is preserved by heat-bath sampling and reinsertion.

Therefore every real test satisfies exact zero source-value influence whenever the changed source is distinct from the resampled fiber.

The same-color remote specialization is formalized by taking the selected fiber to be the target link.

---

# Phase 9 — Identify the only surviving cross-boundary coordinate

**Status: Integrated.**

The diagonal case `source = fiber` is controlled by the sharp right-boundary one-slab Harnack estimate. After normalization, the bounded-test coefficient is

```text
q(beta)
  = 2 * (((Real.exp (8 * beta))^2 - 1)
          / ((Real.exp (8 * beta))^2 + 1)).
```

All off-diagonal source coordinates are exactly zero. Thus the source row is supported at one coordinate and

```text
rowSum = q(beta).
```

No source-cardinality or spatial-volume factor remains.

The explicit threshold

```text
beta_c,C5 = log 3 / 16
```

satisfies

```text
0 <= beta < beta_c,C5
  -> 0 <= q(beta) < 1.
```

No spatial-decay hypothesis is used.

---

# Phase 10 — Package the proved direction as a one-way tagged carrier

**Status: Integrated by the #4141-era carrier.**

The carrier index is

```text
ι_H = Sum Link Link.
```

Interpretation:

```text
Sum.inl = left target copy
Sum.inr = right source copy.
```

Only the proved right-source -> left-target block is populated. Other blocks are zero by carrier definition.

Important semantic boundary:

```text
right-target / left-source = 0 in the tagged carrier
```

does **not** assert that reverse physical influence vanishes.

Both left-target row sums and right-source column sums reduce to the same `q(beta)`; the complementary tagged rows/columns are carrier-scope zero.

---

# Phase 11 — Reciprocal random-scan response

**Status: Integrated.**

Let

```text
N_H = card(ι_H)
r_{H,beta} = finiteInfluenceKernelReciprocalRandomScanRate ι_H q(beta).
```

The exact complement identity is

```text
1 - r_{H,beta} = (1 - q(beta)) / N_H.
```

Hence `r_{H,beta} < 1` at every finite volume in the small-coupling region, but the one-coordinate rate is not uniformly separated from one as `N_H` grows.

The generic variation iteration gives

```text
V_n <= r_{H,beta}^n * V_0.
```

---

# Phase 12 — Genuine stationary non-strict comparison interface

**Status: Integrated conditional interface.**

For genuine finite positive-weight stationary non-strict comparison data `C`, assume its right influence is entrywise dominated by the proved C5 one-way tagged influence.

Then expectation discrepancy is bounded by a C5 partial-source term plus a terminal variation residual.

This theorem deliberately does **not** identify the continuous C5 law with a finite product weight and does not turn carrier-scope zeros into reverse physical theorems.

---

# Phase 13 — Source resolvent and source averaging

**Status: Integrated through PRs #4165, #4168, #4171.**

The reciprocal source resolvent contains an exact cardinality cancellation:

```text
card(ι_H)^-1 * (1-r_{H,beta})^-1
  = (1-q(beta))^-1.
```

Accordingly the accumulated source term is bounded with no extra volume factor:

```text
sum_source partialSource
  <= total(sourceEnvelope) * magnitude * (1-q(beta))^-1.
```

This lifts to source-summed expectation discrepancy, and then to the source-average form

```text
card(ι_H)^-1 * sum_source expectationDiscrepancy
  <=
    (card(ι_H)^-1 * total(sourceEnvelope))
      * magnitude * (1-q(beta))^-1
    + 2 * (r_{H,beta}^n * magnitude).
```

---

# Phase 14 — Convert coordinate time to sweep time

**Status: Integrated by PR #4174.**

The correct volume-independent time scale is a full tagged sweep:

```text
r_{H,beta}^{N_H * sweeps}
  <= exp(-(1-q(beta)) * sweeps).
```

This is the intended scaling statement. It does not claim a uniform one-coordinate rate.

---

# Phase 15 — Stationary source-average with exponential sweep residual

**Status: Integrated by PR #4177.**

Substituting the sweep envelope into the normalized stationary comparison gives

```text
card(ι_H)^-1 * sum_source expectationDiscrepancy
  <=
    (card(ι_H)^-1 * total(sourceEnvelope))
      * magnitude * (1-q(beta))^-1
    + 2 * exp(-(1-q(beta))*sweeps) * magnitude.
```

The explicit terminal residual is volume-independent in sweep time.

The theorem remains conditional on genuine stationary comparison data and entrywise C5 domination. It is not yet a physical Poincare/coercivity theorem.

---

# Phase 16 — Close the normalized source term

**Status: Open now.**

This is the immediate theorem frontier.

The cleanest intermediate target is a uniform normalized source-envelope estimate. For example, derive from actual model structure an estimate of the form

```text
finiteProductVariationTotal sourceEnvelope
  <= card(ι_H) * sigma
```

with `sigma` independent of the relevant volume.

Then #4177 would immediately imply

```text
average expectation discrepancy
  <= sigma * magnitude * (1-q(beta))^-1
     + 2 * exp(-(1-q(beta))*sweeps) * magnitude.
```

A generic corollary formalizing this algebraic discharge is useful only if it is paired with a concrete route for supplying `sigma` from genuine comparison data.

Completion criterion:

```text
volume-independent bound on the normalized source term
```

for the actual comparison carrier needed downstream.

---

# Phase 17 — Realize the physical / spatial coercivity bridge

**Status: Open next.**

The next major bridge must identify how the proved C5 comparison theorem controls the physical spatial conditional dynamics already present in the repository.

Required questions include:

```text
1. Which genuine finite/stationary comparison data represent the relevant physical block?
2. How is their influence dominated by the C5 one-way tagged carrier?
3. What source envelope is produced by the actual model?
4. How does the resulting comparison estimate feed the existing spatial Poincare/coercivity API?
```

Forbidden shortcut:

```text
C5 one-way tagged contraction
  => full physical same-color Poincare inequality
```

without the explicit carrier-identification theorem.

Completion criterion: one model-derived block coercivity theorem with a volume-independent coefficient in the proved small-coupling region.

---

# Phase 18 — Twelve-spatial coercivity and uniform finite-volume gap

**Status: Open downstream; routing already integrated.**

Once the six right and six left block estimates are available, derive a quantitative twelve-spatial Poincare coefficient `kappa(H,N,beta)` and then a scale-independent lower bound

```text
exists kappa_* > 0,
  kappa_* <= kappa(H,N,beta)
```

along the relevant finite-volume/scaling sequence.

The existing routing then gives

```text
physical transfer gap >= 3 * kappa_* / 4.
```

A positive coefficient separately at each finite volume is not enough.

---

# Phase 19 — Thermodynamic / scaling-limit propagation

**Status: Open downstream.**

A uniform finite-volume physical gap must still be transported to the appropriate thermodynamic/scaling-limit physical carrier and connected to a physical OS/Wightman spectral lower bound.

The existing same-root scalar continuum construction is useful infrastructure but is not by itself the complete four-dimensional continuum Yang--Mills gauge field/state.

---

# Phase 20 — Clay-level completion

**Status: Open.**

The final program must still establish the complete continuum Yang--Mills existence statement, the required vacuum/nontriviality structure, and a strictly positive physical spectral gap above the vacuum in the sense required by the Clay problem.

These are mathematical boundaries, not documentation gaps.
