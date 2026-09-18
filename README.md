# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, continuous `SU(N)` one-link laws, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Exact finite-volume statements, one-slab continuous-vacuum constructions, local C5 geometry, fixed-right response identities, restricted-scan transport, cross-ratio normalization, sparse/local contraction interfaces, continuum constructions, and the eventual Clay-level target are kept logically separate.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The continuous `SU(N)` C5 lane has now reached a substantially sharper frontier. Remote fixed-right responses have been reduced at arbitrary finite scan depth to one aggregate tagged profile; an abstract sparse/local restricted-scan contraction with coefficient `18 * eta + rho` and its right-source resolvent are formalized; the actual continuous-vacuum remote cross ratio is bounded by the fixed-right response; targetwise worst cases over all `SU(N)` test values are formalized without assuming supremum attainment; and a generic theorem now converts transformed cross-ratio majorants directly into bounded-test differences of normalized Doob laws.
>
> The immediate open bridge is therefore no longer “find a cross-ratio formula.” It is to specialize that generic Doob theorem to the repository's genuine continuous-vacuum reference one-link conditional kernel, obtain an actual remote one-link influence coefficient, and then discharge the sparse/local residual hypotheses with **concrete volume-uniform `eta` and `rho`**. The older dense distinct-fiber tagged carrier must not be silently reinterpreted as sparse.

---

## Repository authority — documentation baseline 2026-09-18 JST

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The exact merged theorem-carrier commit used to write this documentation is

```text
83f4bc73d01b2cd9f2b6061d8417ebd1b324a3c8
```

with tree

```text
6adda32de936b35b1881d85986773003275e244a
```

This is the merge of PR #4460:

```text
Convert cross-ratio influence majorants to Doob bounded-test control
```

Its exact GREEN proof head was

```text
fe1cd9375b3c1c4523a07242d44af233f13cf0c6
```

The SHA printed here is documentation history, not live authority. This README/ROADMAP refresh is docs-only; after it merges, the branch pointer will move while the latest theorem-bearing mathematical commit remains the latest Lean theorem merge until new theorem work lands.

Always fresh-fetch the theorem-carrier branch before formal work.

Authority order:

```text
1. exact current GitHub SHA on the authoritative theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public/operational landing surface and is not theorem authority when histories differ.

---

# Current proof spine

```text
FINITE WILSON / OS ROOT
  periodic compact SU(N) Wilson model
  -> reflection positivity / OS carriers
  -> one-slab transfer and ground-state structure
  -> conditional-expectation / coercivity interfaces
                                                        [INTEGRATED]

SAME-ROOT SCALAR CONTINUUM OS LANE
  finite Wilson scalar readout
  -> continuum scalar law
  -> reflection positivity
  -> OS Hilbert carrier / C0 semigroup / Hamiltonian
                                                        [INTEGRATED]

CONTINUOUS C5 ONE-LINK / LOCAL GEOMETRY
  normalized continuous SU(N) fiber law
  -> measurable heat-bath reinsertion
  -> represented-source cancellation
  -> intrinsic spatial active-neighbor degree <= 18
  -> C5 exceptional-set cardinality <= 20
                                                        [INTEGRATED]

FIXED-RIGHT RESPONSE / RESTRICTED SCAN
  kernel-section probability law
  -> right update as normalized tilt
  -> two-source / target-ratio response
  -> physical Sum.inl restricted scan
  -> tagged finite-step variation propagation
                                                        [INTEGRATED]

REMOTE AGGREGATION / ARBITRARY-STEP DESCENT
  singleton remote target variations
  -> exact aggregate superposition
  -> arbitrary-n remote response
     <= aggregate right-source iterate
      + 2 * aggregate physical-left total mass
                                                        [INTEGRATED THROUGH #4433]

ABSTRACT SPARSE / LOCAL CLOSURE
  active-neighbor eta + nonnegative residual
  -> left column <= 18*eta + rho
  -> whole-sweep envelope if 18*eta+rho < 1
  -> represented right-source geometric resolvent
                                                        [INTEGRATED INTERFACE #4437/#4439]

NORMALIZATION-AWARE CROSS-RATIO LANE
  target-indexed SU(N) response families
  -> cardinality-free log cross-ratio transform
  -> actual remote vacuum crossRatio <= 1 + exp(16 beta)*ResponseAbs
  -> targetwise transformed columns
  -> targetwise sSup worst cases <= 2
  -> summed worst-case remote column
                                                        [INTEGRATED #4442--#4456]

DOOB BOUNDED-TEST BRIDGE
  transformed pairwise cross-ratio radius <= M, 0<=M<=2
  -> normalized Doob bounded-test difference <= M
  without supremum attainment
                                                        [INTEGRATED #4460]

CURRENT FRONTIER
  specialize the generic Doob bridge to the actual continuous-vacuum
  reference one-link conditional kernel
  -> actual remote one-link influence <= targetwise worst-case majorant
  -> construct concrete sparse/local residual rho
  -> prove 18*eta + rho < 1 in a physical parameter regime
                                                        [OPEN NOW]

DOWNSTREAM
  strict physical restricted-scan response
  -> response certificate / resolvent / sweep closure
  -> physical Poincare / coercivity
  -> uniform finite-volume transfer gap
  -> thermodynamic/scaling-limit physical carrier
  -> sufficiently rich 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                        [OPEN]
```

---

# 1. Continuous C5 geometry: what is already uniform in volume

## 1.1 Represented right-source locality

For the literal continuous C5 one-link law, changing a represented right-boundary source distinct from the resampled physical fiber multiplies the unnormalized one-link density by a scalar independent of the integration variable. Normalization cancels that scalar exactly.

Only the matching represented source survives, with the established coefficient

```text
q(beta)
  = 2 * (exp(16*beta) - 1) / (exp(16*beta) + 1).
```

For

```text
0 <= beta < log 3 / 16
```

one has `q(beta) < 1`.

This is a one-way represented-source theorem. It is **not** a theorem that arbitrary physical left-left influence vanishes.

## 1.2 Bounded local Wilson geometry

The intrinsic spatial active-neighbor degree is bounded by

```text
18
```

uniformly in the periodic volume.

A related C5 exceptional set, after adjoining additional distinguished coordinates, has cardinality bounded by

```text
20.
```

These constants occur in different interfaces and must not be conflated:

- `18` is the active-neighbor degree used by the current sparse/local restricted-scan theorem;
- `20` is an exceptional-set cardinality bound used by older/coarser decompositions.

The current sparse sweep gate is

```text
18 * eta + rho < 1,
```

not a claim that every prior `20 * eta + rho` interface has disappeared.

## 1.3 Dense off-fiber bounds remain fallback bounds only

The older all-links majorant of the form

```text
(card Link - 1) * offFiberInfluence(beta)
```

is mathematically valid as a coarse estimate, but it destroys volume uniformity.

The current program therefore treats the old dense distinct-fiber tagged kernel as a transport majorant only. It must **not** be relabeled as a sparse physical influence kernel.

---

# 2. Remote fixed-right response is reduced to one aggregate tagged profile

The remote target-ratio observable has singleton physical variation concentrated at its target. Summing over remote targets defines one aggregate variation profile.

Exact finite superposition gives, for every tagged coordinate and every finite scan depth `n`,

```text
Q^n(RemoteAggregateVariation)(e)
  = sum_remote Q^n(singleton_target_variation)(e).
```

PR #4433 extends the earlier two-step terminal descent to arbitrary finite `n`. The canonical remote response column now satisfies

```text
RemoteResponseColumn
<= Q^n(RemoteAggregateVariation)(Sum.inr source)
   + 2 *
     sum_{physical e}
       Q^n(RemoteAggregateVariation)(Sum.inl e).
```

This is an exact reduction interface. It does **not** assert decay of either tagged quantity.

The key consequence is conceptual: the stationary response problem is no longer hidden inside an opaque measure discrepancy. It has been reduced to explicit finite-step transport of one aggregate variation profile.

---

# 3. The sparse/local restricted-scan closure interface is already formalized

PR #4437 proves the abstract sparse/local left-block theorem.

Assume a nonnegative physical left-left influence kernel satisfies

```text
K(target,source)
<= (if target is an active spatial neighbor of source then eta else 0)
   + residual(target,source)
```

with

```text
sum_target residual(target,source) <= rho.
```

Then the physical left column satisfies

```text
columnCoefficient <= 18 * eta + rho.
```

If

```text
18 * eta + rho < 1,
```

a whole number of physical-link sweeps has the volume-independent exponential envelope

```text
exp (-(1 - (18*eta + rho)) * sweeps).
```

The one-coordinate reciprocal scan rate still contains the finite-volume reciprocal-card normalization. The **whole-sweep envelope** is what becomes volume-independent.

PR #4439 closes the corresponding accumulated represented-source forcing. Under the same strict gate, the reciprocal-card factor cancels against the geometric resolvent denominator and yields the characteristic factor

```text
(1 - (18*eta + rho))^-1.
```

For the physical-left tagged lift, the initial represented-right value is exactly zero.

These are powerful abstract interfaces, but they do not yet prove that the old dense C5 tagged kernel satisfies the sparse hypotheses.

---

# 4. Target-indexed response quantifiers are complete

PR #4442 removes the artificial requirement that all remote targets share one common `SU(N)` tuple.

The response family now permits independent choices

```text
g1(target), g2(target), h(target), k(target).
```

The arbitrary-step terminal and response reductions remain controlled by the same target-value-independent aggregate tagged right-hand side.

This is the quantifier shape required before taking genuine targetwise worst cases.

---

# 5. The actual remote vacuum cross ratio is tied to fixed-right response

PR #4444 first formalizes the generic cardinality-free normalization algebra

```text
sum_i InfluenceTransform(log(1 + x_i))
<= sum_i x_i
```

for nonnegative `x_i`, together with target-dependent multiplier variants.

PR #4446 then supplies the model-specific bridge. For a geometrically remote target/source pair, the actual continuous-vacuum four-point ratio obeys

```text
crossRatio
<= 1 + exp(16 * beta) * FixedRightTargetRatioResponseAbs.
```

The proof includes the same-target local-factor cocycle, a volume-independent lower bound for the target-ratio average, and the exact cross-ratio / expectation-quotient identity.

This is an actual `SU(N)` normalization-aware theorem. It is still a theorem about the continuous-vacuum one-slab/reference construction, not an identification with an arbitrary full-4D Wilson Gibbs regular conditional probability.

---

# 6. Cross-ratio influence is now target-indexed, worst-case, and remotely summed

PR #4450 transports the model-specific cross-ratio inequality through the canonical full-L1 transform. For arbitrary target-indexed `SU(N)` choices, the transformed remote cross-ratio column is bounded by

```text
exp(16 * beta) * TargetIndexedRemoteResponseColumn,
```

and hence by the arbitrary-step aggregate tagged transport.

PR #4452 then defines, at each target/source pair, the real supremum over all four `SU(N)` test values:

```text
WorstCaseCrossRatioInfluenceMajorant(target,source).
```

The formalization proves:

- the supremum is well-defined without assuming attainment;
- it is bounded above by the canonical full-L1 endpoint `2`;
- for a remote pair it inherits the same target-independent finite-step upper bound.

PR #4456 sums these targetwise suprema over the remote C5 target set **term by term**, without interchanging `sSup` and the finite sum:

```text
WorstCaseRemoteCrossRatioInfluenceColumn
<= exp(16 * beta) *
   (
     Q^n(RemoteAggregateVariation)(Sum.inr source)
     + 2 *
       sum_e Q^n(RemoteAggregateVariation)(Sum.inl e)
   ).
```

No remote-target cardinality multiplier is introduced by the supremum step.

This is the strongest current remote normalization bound. It still does not by itself convert the majorant into the actual one-link conditional influence coefficient.

---

# 7. Generic cross-ratio majorants now control normalized Doob laws

PR #4460 supplies the missing generic measure-theoretic bridge.

Let two normalized Doob laws be generated from one reference measure by positive finite weights `w` and `v`. Suppose a nonnegative logarithmic pairwise cross-ratio radius satisfies

```text
InfluenceTransform(radius(x,y)) <= M
```

for all `x,y`, with

```text
0 <= M <= 2.
```

Then every strongly measurable real test with `|phi| <= 1` obeys

```text
| integral phi d(mu_w) - integral phi d(mu_v) |
<= M.
```

The proof does **not** assume the supremum defining `M` is attained.

It handles the endpoint `M = 2` by the trivial probability bound. For `M < 2`, it uses the inverse Möbius coefficient

```text
K = (2 + M) / (2 - M),
```

converts transformed-radius control to mutual multiplicative domination, and applies the sharp bounded-test comparison theorem.

This theorem closes the generic normalization algebra needed to turn #4452's targetwise worst-case cross-ratio majorant into a genuine bounded-test influence bound.

---

# 8. Current open bridge: actual continuous-vacuum one-link influence

The immediate theorem unit is now precise.

Existing code already identifies the off-target continuous-vacuum reference one-link conditional kernel with a common raw one-slab law reweighted by the continuous-vacuum fiber weight:

```text
conditional law
= doobWeightedMeasure(raw one-slab law, vacuum fiber weight).
```

The remaining specialization must combine:

```text
RemoteVacuumOnlyDoobBridge
+ actual remote vacuum cross-ratio inequality (#4446)
+ targetwise sSup majorant and 0 <= M <= 2 (#4452)
+ generic Doob bounded-test theorem (#4460)
```

to prove, for a remote pair,

```text
actual one-link bounded-test influence(target,source)
<= WorstCaseCrossRatioInfluenceMajorant(target,source).
```

After summing over remote targets, #4456 should then supply the corresponding remote column upper bound.

This is the next normalization/identification step. It must not be described as a full-4D Gibbs RCD theorem unless that stronger identification is separately proved.

---

# 9. What remains before a volume-uniform contraction

Even after the actual one-link influence bridge is closed, one more quantitative step is essential.

The physical left-left influence must be decomposed into

```text
active-neighbor local part <= eta
+ nonnegative remote/vacuum residual
```

with

```text
sum residual <= rho
```

uniformly in periodic volume.

Then the already-merged sparse/local theorem can be instantiated:

```text
18 * eta + rho < 1
-> whole-sweep exponential contraction
-> volume-independent right-source resolvent.
```

The main unresolved issue is therefore **constructing and bounding the concrete physical residual `rho` without feeding the old dense all-links coefficient back into the sparse theorem**.

The #4456 worst-case remote column is designed to be one input to that construction, but its present aggregate tagged RHS is not itself a proof that the dense tagged transport decays sparsely.

---

# 10. Permanent semantic boundaries

These distinctions are part of the repository's proof discipline:

```text
finite theorem != continuum theorem
one-slab/reference conditional kernel != arbitrary full-4D Gibbs RCD
local one-link control != global Poincare inequality

right-boundary cancellation != arbitrary physical left-left cancellation
one-way represented-source influence zero != reverse physical influence zero
Sum.inl physical link != Sum.inr represented source

dense distinct-fiber tagged carrier != sparse physical influence kernel
bounded active-neighbor degree <= 18 != decay of vacuum correlations
exceptional-set cardinality <= 20 != sparse sweep coefficient 18

fixed-right response identity != decay
cross-ratio inequality != conditional-law influence until the Doob bridge is specialized
target-indexed bound != targetwise supremum
targetwise supremum != supremum attainment
sum of targetwise suprema != supremum of a global tuple

arbitrary-step response reduction != volume-uniform contraction
finite superposition != contraction
aggregate remote profile != volume-independent residual bound
abstract 18*eta+rho theorem != concrete SU(N) witness

response-certificate interface != physical witness existence
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

---

# 11. Near-term development order

From canonical theorem baseline #4460, the preferred order is:

```text
1. specialize the generic Doob cross-ratio majorant theorem to the actual
   continuous-vacuum reference one-link conditional kernel;

2. define/prove the actual remote one-link bounded-test influence coefficient
   <= targetwise WorstCaseCrossRatioInfluenceMajorant;

3. sum the actual remote influence column and reuse #4456;

4. construct a physical left-left local-plus-residual decomposition with
   active-neighbor coefficient eta and residual column rho;

5. prove eta and rho are volume-uniform and establish a parameter regime
   satisfying 18*eta + rho < 1;

6. instantiate #4437/#4439 to obtain whole-sweep contraction and the
   represented-source resolvent;

7. feed the strict physical response into the existing response-certificate,
   sweep, conditional-variance, and coercivity machinery;

8. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

9. only then advance the thermodynamic/scaling-limit physical Yang--Mills
   construction and the final spectral mass-gap statement.
```

See [`ROADMAP.md`](ROADMAP.md) for the dependency graph and phase-by-phase obligations.
