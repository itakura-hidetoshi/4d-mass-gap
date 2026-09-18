# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-18 JST**.

The authoritative theorem-carrier branch is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The exact merged theorem-carrier baseline used for this refresh is

```text
83f4bc73d01b2cd9f2b6061d8417ebd1b324a3c8
```

with tree

```text
6adda32de936b35b1881d85986773003275e244a
```

This commit merges PR #4460:

```text
Convert cross-ratio influence majorants to Doob bounded-test control
```

The SHA printed here is documentation history, not live authority. The theorem-carrier branch must be fresh-fetched before theorem work.

Authority order:

```text
1. exact current GitHub theorem-carrier SHA
2. Lean theorem artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is not theorem authority when histories differ.

---

# Dependency graph

```text
A. FINITE PERIODIC WILSON / OS ROOT                           [INTEGRATED]
   -> compact SU(N) finite lattice
   -> reflection positivity / OS carriers
   -> one-slab transfer and ground-state structure
   -> conditional-expectation / coercivity interfaces

B. SAME-ROOT SCALAR CONTINUUM OS LANE                        [INTEGRATED]
   -> scalar readout limits
   -> continuum reflection positivity
   -> OS Hilbert carrier / C0 semigroup / Hamiltonian

C. CONTINUOUS C5 ONE-LINK LAW                                [INTEGRATED]
   -> normalized measurable SU(N) fiber law
   -> exact reinsertion
   -> represented-source cancellation
   -> surviving q(beta)

D. LOCAL C5 GEOMETRY                                         [INTEGRATED]
   -> intrinsic spatial plaquette-neighbor degree <= 18
   -> C5 exceptional set <= 20
   -> remote raw Wilson cancellation

E. FIXED-RIGHT GROUND-STATE RESPONSE                         [INTEGRATED]
   -> positive kernel-section probability law
   -> right update as normalized tilt
   -> two-source crossing response
   -> literal target-ratio response

F. PHYSICAL RESTRICTED-SCAN TRANSPORT                        [INTEGRATED]
   -> deterministic schedules
   -> restricted random scan over Sum.inl only
   -> finite-step expectation iterate
   -> tagged physical variation propagation

G. REMOTE AGGREGATE VARIATION                                [INTEGRATED]
   #4399 source-coordinate aggregate identity
   #4403 pointwise aggregate support
   #4406 all-coordinate finite superposition
   #4409 one-step represented-source aggregate response = 0
   #4412 exact one-step left carrier
   #4415 first nonzero two-step represented-source response
   #4418 volume-independent two-step right-source transport

H. ARBITRARY-STEP TERMINAL / RESPONSE REDUCTION              [INTEGRATED]
   #4421 two-step terminal descent
   #4433 arbitrary-n terminal descent
   -> RemoteResponseColumn
      <= aggregate right-source iterate
       + 2 * aggregate physical-left total mass

I. ABSTRACT SPARSE / LOCAL RESTRICTED-SCAN CLOSURE           [INTEGRATED]
   #4437 active-neighbor eta + residual rho
   -> left column <= 18*eta + rho
   -> full-sweep exponential envelope when < 1
   #4439 right-source resolvent
   -> reciprocal-card cancellation
   -> denominator (1 - (18*eta + rho))^-1

J. TARGET-INDEXED FIXED-RIGHT RESPONSE                       [INTEGRATED]
   #4442 independent targetwise g1,g2,h,k
   -> same aggregate arbitrary-step RHS

K. CARDINALITY-FREE CROSS-RATIO ALGEBRA                      [INTEGRATED]
   #4444 sum transform(log(1+x_i)) <= sum x_i
   -> target-dependent/common multipliers
   -> no finite-family cardinality penalty

L. ACTUAL VACUUM CROSS-RATIO / RESPONSE BRIDGE               [INTEGRATED]
   #4446 actual remote continuous-vacuum cross ratio
   <= 1 + exp(16*beta) * ResponseAbs

M. TARGET-INDEXED CROSS-RATIO TRANSPORT                      [INTEGRATED]
   #4450 chosen targetwise transformed remote cross-ratio column
   <= exp(16*beta) * target-indexed response column
   <= aggregate arbitrary-step tagged transport

N. TARGETWISE WORST-CASE MAJORANTS                           [INTEGRATED]
   #4452 sSup over all targetwise SU(N) test values
   -> nonempty / bounded
   -> 0 <= worst-case majorant <= 2
   -> remote targetwise transport bound
   #4456 sum targetwise sSup majorants over remote family
   -> no sSup/sum exchange
   -> no remote-cardinality factor

O. GENERIC DOOB BOUNDED-TEST BRIDGE                          [INTEGRATED]
   #4460 transformed pairwise cross-ratio radius <= M
   with 0 <= M <= 2
   -> normalized Doob bounded-test difference <= M
   -> endpoint M=2 handled without supremum attainment

P. ACTUAL SU(N) CONDITIONAL-LAW INFLUENCE                    [OPEN NOW]
   off-target reference one-link law
   = raw one-slab law Doob-weighted by vacuum fiber weight
   -> instantiate #4460
   -> actual remote bounded-test influence
      <= targetwise worst-case cross-ratio majorant

Q. CONCRETE PHYSICAL REMOTE COLUMN                           [OPEN NEXT]
   sum_remote physicalRemoteInfluence(target,source)
   -> use #4456
   -> obtain source-summed volume-uniform residual rho

R. PHYSICAL SPARSE / LOCAL COLUMN CLOSURE                    [OPEN NEXT]
   actual left-left influence
   <= active-neighbor eta + residual
   sum residual <= rho
   -> 18*eta + rho < 1
   -> physical whole-sweep contraction
   -> represented-source resolvent

S. PHYSICAL RESPONSE CERTIFICATE / COERCIVITY                [OPEN]
   concrete witnesses
   -> response certificate
   -> source resolvent / sweep
   -> Poincare / coercivity

T. UNIFORM FINITE-VOLUME TRANSFER GAP                        [OPEN]
   volume-independent coercive constant
   -> uniform physical transfer/Hamiltonian gap

U. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                  [OPEN]
   compatible limiting physical states
   -> same-root OS/Wightman carrier
   -> sufficiently rich 4D Yang--Mills field/state
   -> spectral lower bound above vacuum

V. CLAY-LEVEL EXISTENCE + MASS GAP                           [OPEN]
```

---

# Phase 0 — Authority, CI, and proof discipline

**Status: Integrated and permanent.**

For theorem-bearing work:

```text
fresh-fetch authoritative theorem-carrier branch
-> lock exact canonical SHA
-> inspect exact theorem interfaces
-> state the smallest coherent theorem unit
-> run exact-head CI
-> inspect the first genuine Lean error if RED
-> make the smallest proof-preserving fix
-> require completed/success for exact head
-> merge against expected exact head
-> fresh-fetch canonical again
```

Queued or in-progress CI is not GREEN.

GitHub completion comments and commit-status receipts are wake-up/backstop signals only. They are not CI truth, merge authority, or theorem authority. The terminal workflow run, exact head SHA, and terminal job/step conclusion must be fresh-observed before merge.

No new `sorry`, `admit`, axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening may be introduced as a substitute for proof.

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: Integrated.**

The repository contains the finite periodic compact-`SU(N)` Wilson model, lattice geometry, Haar reference measure, Wilson action, reflection-positive structures, one-slab transfer operators, nonnegative ground-state architecture, conditional-expectation carriers, and downstream coercivity interfaces.

This is the finite theorem root. It is not itself a continuum Yang--Mills existence theorem.

---

# Phase 2 — Same-root scalar continuum OS lane

**Status: Integrated as a scalar observable lane.**

The repository contains a same-root scalar continuum construction:

```text
finite Wilson scalar readout
-> continuum scalar law
-> continuum reflection positivity
-> OS Hilbert carrier
-> strongly continuous contraction semigroup
-> self-adjoint Hamiltonian / vacuum structure
```

Boundary: this scalar lane is not yet the full four-dimensional Yang--Mills field/state required for the final problem.

---

# Phase 3 — Continuous C5 one-link law and geometry

**Status: Integrated.**

For represented right-boundary sources:

```text
source != resampled physical fiber
-> source-dependent scalar cancels under normalization
-> represented influence = 0
```

For the matching represented source:

```text
q(beta)
  = 2 * (exp(16*beta)-1)/(exp(16*beta)+1)
```

and

```text
0 <= beta < log 3 / 16
```

implies `q(beta) < 1`.

The bare spatial Wilson geometry supplies:

```text
intrinsic active plaquette-neighbor degree <= 18
C5 exceptional set size <= 20
```

These are local geometry bounds, not correlation-decay theorems.

---

# Phase 4 — Fixed-right response identities

**Status: Integrated.**

The exact chain is:

```text
ground-state kernel section
-> positive finite normalization
-> right update as normalized local tilt
-> covariance response
-> two-source crossing response
-> literal target-ratio specialization
-> remote reference law / kernel-section identity
-> fixed-right target-ratio response
```

These are exact identities. They do not assert decay.

---

# Phase 5 — Physical restricted scan and remote aggregate transport

**Status: Integrated.**

The tagged carrier distinguishes

```text
Sum.inl e = physical left link
Sum.inr s = represented right source
```

and only `Sum.inl` coordinates are scan targets.

The target-ratio observable begins with singleton physical variation

```text
exp(16*beta) at the selected target,
0 elsewhere
```

and the remote aggregate profile is the exact sum of these singleton target profiles.

For every finite depth `n` and every tagged coordinate,

```text
Q^n(RemoteAggregateVariation)(e)
=
sum_remote Q^n(singleton_target_variation)(e)
```

exactly.

This exact superposition remains the algebraic base for all later source-summed bounds.

---

# Phase 6 — Arbitrary-step terminal descent

**Status: Integrated through #4433.**

The two-step terminal theorem of #4421 has been generalized to arbitrary finite scan depth.

The canonical response reduction is

```text
RemoteResponseColumn
<=
Q^n(RemoteAggregateVariation)(Sum.inr source)
+
2 *
sum_{physical e}
  Q^n(RemoteAggregateVariation)(Sum.inl e)
```

for arbitrary `n`.

The terminal measure discrepancy is no longer opaque. The open issue is how to close these tagged quantities uniformly in volume using physical local structure.

---

# Phase 7 — Abstract sparse/local sweep theorem

**Status: Integrated through #4437 and #4439.**

Suppose the physical left-left block admits

```text
influence(target,source)
<=
  activeNeighbor(target,source) * eta
  + residual(target,source)
```

with nonnegative residual and

```text
sum_target residual(target,source) <= rho.
```

Then the intrinsic degree bound gives

```text
leftColumnCoefficient <= 18 * eta + rho.
```

Under

```text
18 * eta + rho < 1
```

the reciprocal random scan contracts over complete physical-link sweeps with envelope

```text
exp (-(1 - (18*eta + rho)) * sweeps).
```

PR #4439 further proves that the accumulated represented-source forcing is bounded by a volume-independent resolvent with denominator

```text
1 - (18 * eta + rho).
```

Boundary: the old dense distinct-fiber carrier is not asserted to satisfy this sparse hypothesis.

---

# Phase 8 — Target-indexed response

**Status: Integrated through #4442.**

The remote response now allows

```text
g1(target), g2(target), h(target), k(target)
```

independently at every remote target.

The same aggregate tagged RHS survives unchanged.

This is the correct quantifier shape for later Dobrushin-style targetwise worst cases.

---

# Phase 9 — Cross-ratio linearization

**Status: Integrated through #4444.**

For any finite nonnegative family,

```text
sum_i InfluenceTransform(log(1 + x_i))
<=
sum_i x_i.
```

No finite-family cardinality factor is introduced.

The theorem also supports target-dependent multipliers and a common multiplier envelope. This is the normalization algebra required to keep source-summed remote influence linear in the response residual.

---

# Phase 10 — Actual continuous-vacuum remote cross ratio

**Status: Integrated through #4446.**

For a geometrically remote target/source pair, the actual continuous-vacuum cross ratio satisfies

```text
crossRatio
<=
1 + exp(16*beta) * ResponseAbs.
```

The proof uses the same-target local-factor cocycle, an `exp(-16*beta)` lower bound for the relevant target-ratio average, and the exact expectation quotient.

This is already a model-specific SU(N) theorem.

Boundary: a cross-ratio estimate is not yet an L1/TV conditional-law influence theorem.

---

# Phase 11 — Target-indexed transformed cross-ratio column

**Status: Integrated through #4450.**

For arbitrary independent targetwise SU(N) tuples,

```text
TargetIndexedRemoteCrossRatioInfluenceColumn
<=
exp(16*beta) * TargetIndexedRemoteResponseColumn
```

and therefore

```text
<=
exp(16*beta) *
[
  aggregate right-source term
  +
  2 * aggregate physical-left total mass
].
```

This is still a chosen-family theorem.

---

# Phase 12 — Targetwise worst-case supremum

**Status: Integrated through #4452.**

At every target/source pair, define

```text
WorstCaseCrossRatioInfluenceMajorant
=
sSup over all g1,g2,h,k in SU(N)
```

of the transformed logarithmic cross-ratio majorant.

The set is nonempty and bounded, and the canonical theorem gives

```text
0 <= WorstCaseCrossRatioInfluenceMajorant <= 2.
```

The remote targetwise worst case is controlled by the same group-value-independent arbitrary-step tagged RHS.

No maximizing tuple is assumed to exist.

---

# Phase 13 — Summed targetwise worst-case remote column

**Status: Integrated through #4456.**

The finite remote column

```text
sum_remote WorstCaseCrossRatioInfluenceMajorant(target,source)
```

is bounded by

```text
exp(16*beta) *
[
  Q^n(RemoteAggregateVariation)(Sum.inr source)
  +
  2 *
  sum_e Q^n(RemoteAggregateVariation)(Sum.inl e)
].
```

The proof is termwise. It does not exchange `sSup` with finite summation.

This closes the source-summed worst-case cross-ratio side once an actual conditional-law influence is shown to lie below the majorant.

---

# Phase 14 — Generic Doob cross-ratio influence theorem

**Status: Integrated through #4460.**

For arbitrary normalized Doob laws built from two weights over one common reference measure, suppose all pairwise logarithmic cross-ratio radii satisfy

```text
InfluenceTransform(radius(x,y)) <= M
```

with

```text
0 <= M <= 2.
```

Then every strongly measurable real test with `|phi| <= 1` satisfies

```text
|E_mu_w phi - E_mu_v phi| <= M.
```

The endpoint `M=2` is handled directly by the probability bound.

For `M<2`, the proof uses

```text
K = (2 + M) / (2 - M)
```

to recover uniform multiplicative domination, then applies the existing sharp normalized-measure bounded-test theorem.

No compactness or supremum attainment is required.

---

# Phase 15 — Actual SU(N) conditional-law influence

**Status: OPEN NOW.**

The repository already proves that the off-target one-link reference conditional law is exactly

```text
doobWeightedMeasure(
  raw one-slab local probability law,
  continuous-vacuum spatial-link fiber weight
).
```

The raw local law is a genuine probability measure. The vacuum fiber weight is continuous, positive, and has finite upper/lower distortion data.

The next theorem should instantiate #4460 for two remote background/source values and prove, for every bounded measurable real test,

```text
actual remote conditional-law bounded-test difference
<=
WorstCaseCrossRatioInfluenceMajorant(target,source).
```

This is the current model-specific normalization bridge.

It must be proved without silently replacing:

```text
fixed-right response
by
actual influence
```

or

```text
cross-ratio majorant
by
TV/L1 coefficient
```

before the Doob theorem has been applied.

---

# Phase 16 — Concrete source-summed physical remote residual

**Status: OPEN NEXT.**

After Phase 15, #4456 yields

```text
sum_remote physicalRemoteInfluence(target,source)
<=
sum_remote WorstCaseCrossRatioInfluenceMajorant(target,source)
```

and therefore an arbitrary-step aggregate tagged upper bound.

The task is to package this as the concrete residual column `rho` needed by the sparse/local physical left-left decomposition.

The desired `rho` must be independent of periodic volume.

---

# Phase 17 — Physical sparse/local closure

**Status: OPEN NEXT.**

The concrete target is

```text
physicalLeftInfluence(target,source)
<=
  activeNeighbor(target,source) * eta
  + vacuumResidual(target,source),
```

with

```text
sum_target vacuumResidual(target,source) <= rho
```

uniformly in source and volume.

Then the already-integrated theorem gives

```text
leftColumn <= 18 * eta + rho.
```

The decisive contraction milestone is a concrete physical regime satisfying

```text
18 * eta + rho < 1.
```

An older exceptional-set interface involving `20 * eta + rho` remains available where its own hypotheses are used. It is not the same theorem as the intrinsic active-neighbor sparse gate.

---

# Phase 18 — Response certificate, resolvent, and sweep closure

**Status: OPEN DOWNSTREAM.**

Once the actual physical sparse/local witnesses are available:

```text
physical influence witnesses
-> strict left-column coefficient
-> whole-sweep contraction
-> represented-source resolvent
-> response certificate
-> quantitative response closure
```

The abstract algebra is now substantially ahead of the model-specific witness construction.

---

# Phase 19 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

The intended route is

```text
strict continuous physical response control
-> block / conditional variance estimate
-> physical Poincare or coercivity inequality
-> volume-uniform transfer-sector control
```

This must be instantiated with actual continuous `SU(N)` quantities.

---

# Phase 20 — Uniform finite-volume transfer gap

**Status: OPEN DOWNSTREAM.**

The required target is a scale-independent constant

```text
kappa_* > 0
```

producing a physical transfer/Hamiltonian spectral lower bound uniform over the periodic volumes used in the limiting construction.

A positive gap whose constant collapses with volume is insufficient.

---

# Phase 21 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap is established, the remaining program includes

```text
compatible limiting physical states
-> same-root OS/Wightman carrier
-> limiting semigroup / Hamiltonian
-> sufficiently rich nontrivial 4D Yang--Mills field/state
-> spectral lower bound above the vacuum
```

The existing scalar continuum OS lane is same-root infrastructure, not a substitute for the full gauge-field construction.

---

# Phase 22 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The present repository contains a large formal proof spine and a substantially sharpened continuous-`SU(N)` quantitative response program, but the final claim remains open until the physical conditional-law influence, volume-uniform sparse/local closure, coercivity, finite-volume uniform gap, and limiting field/state obligations are all discharged.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4460:

```text
1. instantiate the generic Doob cross-ratio theorem for the actual remote
   continuous-SU(N) one-link conditional laws;

2. prove
     physicalRemoteInfluence(target,source)
     <= WorstCaseCrossRatioInfluenceMajorant(target,source);

3. sum the physical remote column using the already-merged #4456 theorem;

4. define the concrete vacuum residual and prove a source-summed
   volume-uniform bound rho;

5. combine the physical residual with the active-neighbor local term eta;

6. prove a concrete regime with 18*eta + rho < 1;

7. instantiate the whole-sweep contraction and represented-source resolvent;

8. close the physical response certificate / Poincare / coercivity route;

9. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

10. only then advance the thermodynamic/continuum physical Yang--Mills limit
    and final mass-gap statement.
```

The current conceptual transition is:

```text
#4433:
  stationary remote response reduced at arbitrary finite depth

#4437/#4439:
  sparse/local sweep and source resolvent available abstractly

#4442:
  correct target-indexed response quantifiers

#4446/#4450:
  actual SU(N) vacuum cross ratio transported into the response algebra

#4452/#4456:
  targetwise worst-case remote cross-ratio majorants summed without
  cardinality loss

#4460:
  generic cross-ratio majorant -> normalized Doob bounded-test control

current frontier:
  apply that generic theorem to the actual SU(N) one-link conditional laws,
  then construct the concrete physical residual rho needed by the sparse gate.
```
