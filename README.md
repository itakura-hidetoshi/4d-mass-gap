# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectations, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Exact finite-volume Wilson/OS results, continuous-state one-link laws, local C5 geometry, fixed-right ground-state response identities, restricted-scan transport, cross-ratio normalization, coercivity routing, continuum constructions, and the eventual Clay-level target are kept logically separate.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current continuous `SU(N)` C5 lane has now reached a sharper point than the earlier dense-Harnack stage. Arbitrary finite-depth terminal response has been reduced to an aggregate tagged transport; sparse/local sweep and right-source resolvent interfaces are formalized abstractly; the fixed-right response has been strengthened to target-indexed worst cases; the actual continuous-vacuum remote cross ratio is bounded by the fixed-right response; targetwise supremum cross-ratio majorants have been summed without a remote-cardinality penalty; and a generic theorem now converts transformed cross-ratio majorants into bounded-test control for normalized Doob laws.
>
> The immediate missing theorem is therefore no longer the normalization algebra itself. It is the **model-specific application identifying the actual remote one-link conditional-law influence with, or bounding it by, the targetwise worst-case cross-ratio majorant**, followed by a concrete sparse/local residual-column estimate `rho` that closes the physical left-left column uniformly in volume.

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

This README/ROADMAP refresh is docs-only. Once merged, the branch pointer will advance even though the latest theorem-bearing mathematical baseline remains the latest Lean theorem merge until another theorem PR lands. Therefore **always fresh-fetch the theorem-carrier branch before theorem work**. A SHA printed in documentation is historical provenance, not live authority.

Authority order:

```text
1. exact current GitHub SHA on the authoritative theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public landing surface and CI/infrastructure home; it is not theorem authority when histories differ.

---

# Current proof spine

```text
FINITE PERIODIC WILSON / OS ROOT
  compact SU(N) Wilson model
  -> reflection positivity / OS carriers
  -> one-slab transfer and ground-state structure
  -> conditional-expectation / coercivity routing
                                                        [INTEGRATED]

SAME-ROOT SCALAR CONTINUUM OS LANE
  finite Wilson scalar readout
  -> continuum scalar law
  -> reflection positivity
  -> OS Hilbert carrier / C0 semigroup / Hamiltonian
                                                        [INTEGRATED]

CONTINUOUS C5 ONE-LINK LAW + LOCAL GEOMETRY
  normalized continuous SU(N) fiber law
  -> measurable heat-bath reinsertion
  -> represented-source cancellation
  -> local plaquette-neighbor degree <= 18
  -> C5 exceptional set <= 20
                                                        [INTEGRATED]

FIXED-RIGHT GROUND-STATE RESPONSE
  kernel-section probability law
  -> normalized right-boundary tilt
  -> two-source crossing response
  -> literal remote target-ratio response
                                                        [INTEGRATED]

PHYSICAL RESTRICTED-SCAN TRANSPORT
  deterministic schedules
  -> restricted random scan over physical Sum.inl fibers
  -> tagged finite-step variation transport
  -> exact remote aggregate superposition
                                                        [INTEGRATED]

ARBITRARY-STEP RESPONSE REDUCTION
  RemoteResponseColumn
    <= aggregate right-source term
     + 2 * aggregate physical-left total mass
                                                        [INTEGRATED #4433]

SPARSE / LOCAL ABSTRACT CLOSURE
  active-neighbor eta + residual rho
  -> left column <= 18*eta + rho
  -> full-sweep exponential envelope if < 1
  -> volume-independent represented-source resolvent
                                                        [INTEGRATED #4437/#4439]

TARGET-INDEXED FIXED-RIGHT RESPONSE
  independent SU(N) values at every remote target
  -> same aggregate transport RHS
                                                        [INTEGRATED #4442]

CROSS-RATIO NORMALIZATION
  actual remote continuous-vacuum cross ratio
  <= 1 + exp(16*beta) * fixed-right ResponseAbs
  -> log / influence transform
  -> finite-sum linearization without cardinality loss
                                                        [INTEGRATED #4444/#4446/#4450]

TARGETWISE WORST CASE
  sSup over g1,g2,h,k at each target
  -> 0 <= majorant <= 2
  -> targetwise arbitrary-step aggregate bound
  -> summed worst-case remote column
                                                        [INTEGRATED #4452/#4456]

GENERIC DOOB INFLUENCE BRIDGE
  transformed cross-ratio radius <= M, 0 <= M <= 2
  -> normalized Doob bounded-test difference <= M
  without supremum attainment
                                                        [INTEGRATED #4460]

CURRENT MODEL-SPECIFIC FRONTIER
  actual remote one-link conditional laws
  -> instantiate generic Doob bridge with SU(N) vacuum fiber weights
  -> physical remote influence <= targetwise worst-case majorant
  -> source-summed concrete residual column rho
                                                        [OPEN NOW]

PHYSICAL SPARSE / LOCAL CLOSURE
  active-neighbor contribution + vacuum residual
  -> strict volume-independent physical column contraction
  -> source resolvent / sweep / coercivity
                                                        [OPEN]

DOWNSTREAM
  physical Poincare / coercivity
  -> uniform finite-volume transfer gap
  -> thermodynamic/scaling-limit physical carrier
  -> sufficiently rich 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                        [OPEN]
```

---

# 1. What is already volume-independent

## 1.1 Exact represented right-source locality

For the literal continuous C5 one-link law, changing a represented right-boundary source distinct from the resampled physical fiber multiplies the unnormalized one-link density by a scalar independent of the integration variable. Normalization cancels that scalar exactly.

Only the matching represented source survives, with coefficient

```text
q(beta)
  = 2 * (exp(16*beta) - 1) / (exp(16*beta) + 1).
```

Hence

```text
0 <= beta < log 3 / 16
```

implies

```text
q(beta) < 1.
```

This is a one-way represented-source statement. It is **not** a theorem that arbitrary physical left-left influence vanishes.

## 1.2 Bounded local Wilson geometry

For a spatial link, the number of distinct intrinsic spatial links sharing a spatial Wilson plaquette is at most

```text
18.
```

After adjoining the resampled fiber and distinguished right target, the relevant C5 exceptional set has cardinality at most

```text
20
```

uniformly in periodic volume.

The number 18 belongs to the intrinsic active-neighbor left-left geometry. The number 20 belongs to the older exceptional-set decomposition. They are related but are not interchangeable theorem hypotheses.

## 1.3 The dense off-fiber majorant is not the sparse model

The older coefficient

```text
(card Link - 1) * offFiberInfluence(beta)
```

remains a valid coarse dense bound.

It is **not** the carrier used to justify the sparse/local theorem of #4437. The formalization explicitly keeps these objects separate. Treating the dense distinct-fiber carrier as sparse would reintroduce the volume factor and would be a semantic error.

---

# 2. Arbitrary finite-depth stationary response is reduced to tagged transport

PR #4433 generalized the earlier two-step terminal descent to arbitrary finite restricted-scan depth `n`.

For the remote target family, the current theorem gives the schematic bound

```text
RemoteResponseColumn
<=
  Q^n(RemoteAggregateVariation)(Sum.inr source)
  +
  2 *
  sum_{physical e}
    Q^n(RemoteAggregateVariation)(Sum.inl e).
```

The finite-depth right-source term and the propagated physical-left total mass are now the complete explicit obstruction. No opaque terminal probability-law discrepancy remains in this reduction.

This theorem does **not** itself assert decay of either term.

---

# 3. Sparse/local restricted-scan closure exists as an abstract theorem

PR #4437 formalized the sparse/local left-left mechanism independently of the old dense carrier.

Assume a physical left-left influence kernel satisfies

```text
influence(target,source)
<=
  [target is an active plaquette neighbor of source] * eta
  + residual(target,source),
```

with nonnegative residual and

```text
sum_target residual(target,source) <= rho.
```

Using the intrinsic degree bound, the physical-left column coefficient obeys

```text
columnCoefficient <= 18 * eta + rho.
```

If

```text
18 * eta + rho < 1,
```

then a whole physical-link sweep has the volume-independent exponential envelope

```text
exp (-(1 - (18*eta + rho)) * sweeps).
```

The one-step reciprocal random-scan rate still contains the finite-volume reciprocal-card normalization; the full-sweep estimate is the volume-independent object.

PR #4439 then formalized the corresponding represented-right source resolvent. Under the same strict gate, reciprocal-card normalization cancels against the geometric resolvent denominator, producing a volume-independent accumulated source-forcing bound with denominator

```text
1 - (18 * eta + rho).
```

These are abstract carrier theorems. They do not yet prove that the physical continuous-vacuum left-left influence has such a decomposition.

---

# 4. The fixed-right response now has the correct Dobrushin quantifiers

PR #4442 replaced the old common global tuple

```text
g1, g2, h, k
```

with independently chosen targetwise functions

```text
g1(target), g2(target), h(target), k(target).
```

The complete arbitrary-step response reduction survives unchanged:

```text
target-indexed remote response
<=
aggregate right-source transport
+
2 * aggregate physical-left total mass.
```

The right-hand side is independent of the targetwise group values.

This is the quantifier shape required before taking genuine targetwise worst cases.

---

# 5. The actual SU(N) remote vacuum cross ratio is controlled by fixed-right response

PR #4446 established the model-specific normalization bridge that was previously missing.

For a geometrically remote target/source pair, the actual continuous-vacuum four-point cross ratio is bounded by

```text
crossRatio(target,source; g1,g2,h,k)
<=
1 + exp(16*beta) * ResponseAbs(target,source; g1,g2,h,k).
```

The proof includes:

```text
same-target local-factor cocycle,
volume-independent exp(-16*beta) lower bound for target-ratio averages,
exact cross-ratio / expectation-quotient identity,
fixed-right response upper bound.
```

This is a theorem about the actual continuous-vacuum ratio. It does not by itself identify an L1 conditional-law influence coefficient.

---

# 6. Logarithmic cross-ratio influence is cardinality-free

PR #4444 formalized the generic finite-family inequality

```text
sum_i InfluenceTransform(log(1 + x_i))
<=
sum_i x_i
```

for nonnegative `x_i`, with no extra cardinality multiplier.

It also supports target-dependent multipliers and a common multiplier envelope.

Combining #4446 with this algebra, PR #4450 proved for arbitrary independently chosen targetwise SU(N) tuples that the transformed remote cross-ratio column is bounded by

```text
exp(16*beta) * TargetIndexedRemoteResponseColumn,
```

and therefore by the same arbitrary-step aggregate tagged transport from #4433.

This is still a chosen-family statement at this stage.

---

# 7. Targetwise worst-case cross-ratio majorants are now canonical

PR #4452 closed the chosen-family / worst-case quantifier gap.

For each target/source pair, define the transformed cross-ratio majorant set over all four SU(N) test values and take the real supremum

```text
WorstCaseCrossRatioInfluenceMajorant(target,source)
  = sSup { transformed majorants over g1,g2,h,k }.
```

The formalization proves the set is nonempty and bounded and that

```text
0 <= WorstCaseCrossRatioInfluenceMajorant <= 2.
```

No compactness or supremum attainment is required.

For remote target/source pairs, the targetwise worst case is bounded by the same SU(N)-independent arbitrary-step tagged transport.

PR #4456 then summed these targetwise suprema over the finite remote target family:

```text
sum_remote WorstCaseCrossRatioInfluenceMajorant(target,source)
<=
exp(16*beta) *
[
  Q^n(RemoteAggregateVariation)(Sum.inr source)
  +
  2 * sum_e Q^n(RemoteAggregateVariation)(Sum.inl e)
].
```

The proof applies the uniform targetwise bound term by term. It does **not** exchange `sSup` with the finite sum and introduces no remote-target cardinality factor.

---

# 8. Generic cross-ratio majorants now control normalized Doob laws

PR #4460 supplies the generic measure-theoretic bridge needed for actual conditional-law influence.

Let `w` and `v` be two nonnegative weights over a common reference measure. Suppose their normalized Doob laws are genuine probability measures and that for every pair `x,y` there is a nonnegative logarithmic cross-ratio radius `r(x,y)` satisfying the pointwise multiplicative cross-ratio inequality.

If

```text
InfluenceTransform(r(x,y)) <= M
```

for all `x,y`, with

```text
0 <= M <= 2,
```

then every strongly measurable real test `phi` with

```text
|phi| <= 1
```

satisfies

```text
| integral phi d(mu_w) - integral phi d(mu_v) |
<= M.
```

The proof deliberately avoids assuming that a supremum is attained.

At the endpoint `M = 2`, the theorem uses the trivial probability bound. For `M < 2`, it inverts the canonical transform using

```text
K = (2 + M) / (2 - M),
```

derives mutual multiplicative domination of the two normalized Doob measures, and applies the sharp bounded-test comparison theorem.

This generic normalization algebra is now complete.

---

# 9. Current frontier: actual SU(N) conditional-law influence

The next theorem is model-specific.

The repository already contains the exact off-target bridge

```text
actual reference one-link conditional law
=
doobWeightedMeasure(raw one-slab local law, continuous-vacuum fiber weight).
```

For two remote background configurations differing at a source link, the intended next step is to instantiate #4460 with the two continuous-vacuum fiber weights and the same raw local one-link law.

The target statement is schematically

```text
for every |phi| <= 1,

| E_{conditional law after source=u}[phi]
  - E_{conditional law after source=v}[phi] |

<= WorstCaseCrossRatioInfluenceMajorant(target,source).
```

Equivalently, the actual remote one-link bounded-test influence should be bounded by the already-formalized targetwise worst-case cross-ratio majorant.

The required ingredients are already present separately:

```text
raw one-slab link law is a probability measure,
continuous-vacuum fiber weights are continuous and positive,
finite positive upper/lower distortion bounds exist,
off-target conditional law = raw-law vacuum Doob reweighting,
actual vacuum cross ratio has the fixed-right response majorant,
WorstCaseCrossRatioInfluenceMajorant lies in [0,2],
generic Doob bounded-test theorem handles M=2 without attainment.
```

The application theorem itself is **not yet merged** at this baseline.

---

# 10. After the actual conditional-law bridge

Once the model-specific inequality

```text
physicalRemoteInfluence(target,source)
<=
WorstCaseCrossRatioInfluenceMajorant(target,source)
```

is available, #4456 immediately supplies a source-summed remote majorant in terms of the arbitrary-step aggregate tagged transport.

The next quantitative obligation is then to discharge the abstract sparse/local hypotheses with actual continuous-`SU(N)` data:

```text
physical left-left influence
<= active-neighbor eta + vacuum residual,

sum residual <= rho,

18 * eta + rho < 1.
```

This is where the current abstract sparse/local sweep theorem and right-source resolvent become physically instantiated.

A different older interface based on the C5 exceptional set yields a bound of the form

```text
20 * eta + rho.
```

That interface remains valid where its hypotheses are used, but the present sparse left-left closure is organized around the intrinsic active-neighbor coefficient `18 * eta + rho`. The two constants should not be silently conflated.

---

# 11. What remains open

The remaining program is now concentrated in the following order:

```text
1. instantiate #4460 for the actual remote SU(N) one-link conditional laws;

2. define/bound the actual physical remote influence coefficient by the
   targetwise worst-case cross-ratio majorant;

3. sum over remote targets using #4456;

4. prove a concrete sparse/local physical residual column rho, uniformly
   in periodic volume;

5. establish a strict gate such as 18*eta + rho < 1 for the relevant
   physical left-left carrier;

6. instantiate the existing right-source resolvent / sweep / response
   machinery with the concrete physical witnesses;

7. derive physical Poincare/coercivity with a volume-independent constant;

8. derive a uniform finite-volume physical transfer/Hamiltonian gap;

9. construct and control the thermodynamic/scaling-limit physical
   Yang--Mills carrier and sufficiently rich field/state content;

10. only then close the Clay-level existence and mass-gap statement.
```

---

# 12. Permanent semantic boundaries

These distinctions are part of the repository's proof discipline:

```text
finite theorem != continuum theorem
local one-link control != global Poincare inequality
represented right-source cancellation != physical left-left cancellation
one-way tagged zero block != reverse physical influence zero
Sum.inl physical link != Sum.inr represented source
full tagged scan != physical restricted random scan
dense distinct-fiber carrier != sparse active-neighbor carrier
bounded Wilson degree != decay of ground-state correlations
exact covariance identity != covariance decay
fixed-right response != actual conditional-law influence
cross-ratio majorant != already-proved L1 influence
target-indexed bound != supremum attainment
sSup bound != existence of a maximizing tuple
finite superposition != contraction
aggregate remote profile != volume-independent left-mass closure
abstract 18*eta+rho gate != concrete SU(N) verification
response certificate != physical witness existence
uniform finite-volume gap != thermodynamic/continuum mass gap
same-root scalar continuum != complete 4D Yang--Mills field/state
formal intermediate theorem != Clay-level completion
```

See [`ROADMAP.md`](ROADMAP.md) for the phase-by-phase dependency graph and immediate theorem order.
