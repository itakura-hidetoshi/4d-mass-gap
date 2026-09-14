# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately conservative about claims. Exact finite-volume theorems, almost-everywhere bridges, conditional-law identifications, quantitative comparison inputs, continuum constructions, and the final Clay-level target are kept logically separate.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current finite-volume program has, however, moved substantially beyond the earlier remote-influence bottleneck. For the literal C5 reference one-link law, distinct right-boundary source values are now proved to cancel **exactly after normalization** whenever `source != fiber`. The corresponding conditional and heat-bath carriers are literally equal, so the off-diagonal C5 cross-boundary influence is zero.
>
> The only remaining C5 cross-boundary bounded-test contribution is the matching coordinate `source = fiber`. Its complete source row collapses to the single coefficient
>
> ```text
> q(beta)
>   = 2 * (((exp (8*beta))^2 - 1) / ((exp (8*beta))^2 + 1))
>   = 2 * (exp (16*beta) - 1) / (exp (16*beta) + 1),
> ```
>
> with no spatial-volume or color-class cardinality factor. The explicit threshold
>
> ```text
> beta < log 3 / 16
> ```
>
> implies `q(beta) < 1`.
>
> This contraction has been packaged as a **one-way tagged** carrier on `Sum Link Link`, propagated through generic reciprocal random-scan comparison machinery, and lifted to a source-averaged stationary comparison with a sweep-scaled exponential residual.
>
> The current unresolved step is therefore **not** to invent spatial exponential decay. It is to close the remaining normalized stationary source term and identify the genuine finite positive-weight / physical comparison data needed to connect the proved C5 carrier to the existing spatial Poincare/coercivity route.

---

## Repository authority — 2026-09-15 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest mathematical theorem baseline before this documentation refresh:
  b7bf4dc6e590f88c64e5a01d018da60155e8ace5

This is the merge of:
  PR #4177
  Lift C5 stationary average to sweep exponential residual

Exact final GREEN proof head:
  68fbb3385b7e3470ed7bb041c7e86efab69da286

Validation receipt:
  PR Lean Fast Check #13887
  workflow run 34908048470
  workflow / job / changed-Lean step: completed / success

Tree at that theorem baseline:
  8c7cb7aade0be712df53702613f5b9fade64c699

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

`main` is a public landing surface, not theorem authority when histories differ. A docs-only merge may advance the theorem-carrier branch pointer beyond the mathematical baseline above without changing the latest theorem-bearing result.

---

# Proof architecture in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> spatial-slice and boundary L2 carriers
  -> physical one-slab transfer / ground-state structure
                                                               [INTEGRATED]

B. SAME-ROOT SCALAR CONTINUUM OS LANE

finite Wilson scalar readout
  -> same-root continuum scalar probability law
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

constant pairwise remote bound
  -> same nonzero coefficient at every remote source
  -> row sum grows with remote-link cardinality
                                                               [OBSTRUCTION INTEGRATED]

F. LOCALITY / CONDITIONAL-LAW INFRASTRUCTURE

raw same-color Wilson cancellation
  -> covariance / cross-ratio localization
  -> literal normalized reference one-link fiber
  -> measurable heat-bath kernel
  -> off-fiber conditional expectation / condExpKernel / RCD
  -> conditional-variance transport
                                                               [INTEGRATED]

G. C5 RAW-DOOB / SOURCE FACTORIZATION

literal C5 fiber weight
  = Omega_cont x target-local x source-sensitive one-slab kernel
  -> normalized raw law
  -> exact continuous-vacuum Doob composition
  -> quotient-free two-source cross-ratio
  -> explicit K_1-K_2 carrier
  -> distinct-source scalar factorization
                                                               [INTEGRATED]

H. DISTINCT-SOURCE NORMALIZED INVARIANCE

source != fiber
  -> W_k(g) = c_k * W_base(g),  c_k > 0 and independent of g
  -> Z_k = c_k * Z_base
  -> scalar cancels from normalized fiber measure
  -> conditional kernel equality
  -> heat-bath kernel equality
  -> every real-test influence = 0
                                                               [INTEGRATED]

I. C5 CROSS-BOUNDARY SUPPORT / ROW CONTRACTION

off-diagonal sources: exact zero
matching source = fiber: diagonal Harnack residual
  -> source row supported on one coordinate
  -> row sum = q(beta), no volume factor
  -> beta < log 3/16 => q(beta) < 1
                                                               [INTEGRATED]

J. ONE-WAY TAGGED CARRIER

index ι_H = Sum Link Link
  left target / right source = proved C5 influence
  all other blocks = carrier-scope zero only
  -> every tagged row bounded by q(beta)
  -> every tagged column bounded by q(beta)
  -> reciprocal random-scan variation iteration
                                                               [INTEGRATED]

K. STATIONARY COMPARISON / RESOLVENT

genuine finite positive-weight stationary non-strict comparison data
+ entrywise domination by C5 tagged carrier
  -> kernel residual bound
  -> exact source-resolvent cardinality cancellation
  -> source-summed expectation-discrepancy bound
  -> source-average normalization
                                                               [INTEGRATED, CONDITIONAL INTERFACE]

L. SWEEP-SCALED RESIDUAL

r_{H,beta} = reciprocal one-coordinate random-scan rate

r_{H,beta}^{card(ι_H) * sweeps}
  <= exp(-(1-q(beta)) * sweeps)

therefore

average source expectation discrepancy
  <= normalized source resolvent
     + 2 * exp(-(1-q(beta))*sweeps) * magnitude
                                                               [#4177 INTEGRATED]

M. PRESENT FRONTIER

close / bound normalized sourceEnvelope uniformly
+ construct or identify the genuine comparison data controlled by C5
  -> connect to existing spatial Poincare / coercivity carrier
  -> one color-block coercivity
  -> six-right + six-left block coercivity
  -> quantitative E12 Poincare coefficient
                                                               [OPEN NOW]

N. DOWNSTREAM MASS-GAP ROUTE

scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4
  -> thermodynamic / scaling-limit physical carrier
  -> physical OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                               [OPEN]
```

---

# 1. What changed after the earlier C5 scalar-factorization frontier

The earlier roadmap stopped at the observation that a distinct right-boundary source update factors through a scalar independent of the selected fiber variable. That observation is no longer merely suggestive.

The current theorem tree proves the full normalized cancellation:

```text
source != fiber
  -> source-sensitive fiber weight = positive scalar * common base weight
  -> partition function scales by the same scalar
  -> normalized C5 fiber probability measures are equal.
```

This is a measure-level equality, before taking expectations or defining an influence coefficient.

The equality then propagates to the measurable conditional kernel and the full heat-bath sampling/reinsertion kernel. Consequently every real test has exactly zero source-value influence for a source distinct from the selected fiber.

This is stronger than a distance-decay estimate, but it is specific to the proved C5 conditional carrier and its stated source/fiber geometry.

---

# 2. Cross-boundary support is exactly diagonal

For `source = fiber`, the source update does not cancel. The two literal C5 fiber weights obey the sharp one-slab pairwise Harnack comparison with factor

```text
exp(8 * beta).
```

After normalization, mutual domination carries the squared factor. The resulting bounded-test coefficient is

```text
q(beta)
  = 2 * (((exp (8*beta))^2 - 1) / ((exp (8*beta))^2 + 1)).
```

For `source != fiber`, the coefficient is exactly zero. Therefore the full finite source row has one-point support and

```text
rowSum = q(beta).
```

There is no factor proportional to the number of links, sources, or color-class elements.

The explicit theorem-defined threshold is

```text
beta_c,C5 = log 3 / 16,
```

and for nonnegative `beta < beta_c,C5`,

```text
0 <= q(beta) < 1.
```

This closes the earlier link-count obstruction **for this exact C5 cross-boundary carrier** without assuming spatial decay.

---

# 3. The one-way tagged carrier and its semantic boundary

The proved cross-boundary direction is packaged on

```text
ι_H = Sum Link Link.
```

The left copy is the target copy and the right copy is the source copy. Only

```text
right-source -> left-target
```

is represented by the C5 influence coefficient.

The remaining tagged blocks are zero because they are outside the carrier definition. In particular,

```text
right-target / left-source = 0
```

inside this tagged object is **not** a theorem that the reverse physical influence vanishes.

Likewise, `Sum.inl link` and `Sum.inr link` are distinct tagged coordinates and must not be collapsed to one untagged link index.

The carrier has both row and column bounds by the same volume-independent `q(beta)`.

---

# 4. Random-scan contraction: what is and is not volume-independent

Let

```text
N_H = card(ι_H)
r_{H,beta} = finiteInfluenceKernelReciprocalRandomScanRate ι_H q(beta).
```

The exact reciprocal complement is

```text
1 - r_{H,beta} = (1 - q(beta)) / N_H.
```

Therefore the one-coordinate rate `r_{H,beta}` approaches one as the tagged volume grows. The repository does **not** claim a volume-uniform one-coordinate contraction factor bounded away from one.

The correct volume-independent statement uses full-sweep time:

```text
r_{H,beta}^{N_H * sweeps}
  <= exp(-(1-q(beta)) * sweeps).
```

This is the scaling used by the current stationary comparison theorem.

---

# 5. Stationary comparison and exact source-resolvent cancellation

The C5 tagged carrier is connected to a generic finite positive-weight stationary non-strict comparison interface.

The interface assumes genuine comparison data `C` and entrywise domination of its right influence by the C5 one-way tagged carrier. It does **not** identify the continuous C5 one-slab law with a finite-state model by definition.

The source-resolvent layer proves an exact cardinality cancellation. After summing over sources, the tagged-card normalization and reciprocal random-scan resolvent combine to leave

```text
(1 - q(beta))^-1
```

rather than a growing volume factor.

For a family of singleton-variation observables, this yields a source-summed expectation-discrepancy estimate, then a source-average estimate in which the terminal explicit cardinality also cancels.

---

# 6. Current #4177 estimate

In the small-coupling C5 region, the merged theorem chain gives the normalized stationary source-average form

```text
card(ι_H)^-1 * sum_source expectationDiscrepancy
  <=
    (card(ι_H)^-1 * total(sourceEnvelope))
      * magnitude * (1-q(beta))^-1
    + 2 * exp(-(1-q(beta))*sweeps) * magnitude.
```

The second term is explicitly volume-independent once random-scan time is measured in full tagged sweeps.

The first term is also normalized by tagged cardinality, but it remains an input through `sourceEnvelope`. Closing or controlling this term uniformly is the immediate mathematical interface to the next stage.

---

# 7. Present frontier

The next coherent proof objective is to remove the remaining conditionality **without overstating what the C5 carrier proves**.

A clean route is:

```text
proved C5 one-way tagged influence
  -> genuine stationary comparison data for the relevant physical carrier
  -> uniform bound on normalized sourceEnvelope
  -> stationary comparison with fully volume-independent right-hand side
  -> spatial/block Poincare or coercivity bridge
  -> quantitative twelve-spatial coefficient.
```

A particularly useful intermediate theorem would be a normalized-source corollary of the form

```text
finiteProductVariationTotal sourceEnvelope
  <= card(ι_H) * sigma
```

implying

```text
average discrepancy
  <= sigma * magnitude * (1-q(beta))^-1
     + 2 * exp(-(1-q(beta))*sweeps) * magnitude,
```

provided `sigma` can then be supplied from the actual model.

This would still be an interface theorem until the required genuine comparison data and physical coercivity bridge are discharged.

---

# 8. Permanent claim boundaries

The repository currently does **not** prove any of the following merely from the C5 stationary comparison chain:

- that the C5 raw one-slab law equals the full-4D Wilson `singleLinkConditionalMeasure`;
- that the unrepresented reverse left-to-right physical influence is zero;
- that every full-4D same-color influence matrix equals the C5 one-way tagged carrier;
- that the one-coordinate reciprocal random-scan rate is volume-uniform;
- that the normalized stationary source envelope already has a uniform physical bound;
- that #4177 is itself a physical Poincare or coercivity theorem;
- a scale-independent twelve-spatial Poincare coefficient;
- a uniform finite-volume physical transfer gap obtained from that coefficient;
- the required thermodynamic/scaling-limit physical carrier with inherited positive gap;
- the complete four-dimensional continuum Yang--Mills field/state required by the Clay formulation;
- Clay-level existence and mass gap.

No spatial estimate of the form `C * exp(-m*d)` is assumed by the current C5 contraction route.

---

# 9. Reading order

For the theorem-development order and the exact next proof frontier, see [`ROADMAP.md`](ROADMAP.md).

For theorem authority, always inspect the exact current HEAD of

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

before relying on a historical SHA recorded in prose.
