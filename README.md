# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Current theorem frontier — through merged PR #4971:** the actual right/left tagged one-link dynamics on the genuine Wilson ground-state joint L2 carrier now satisfy a volume-independent, all-L2 **relative Poincare inequality to the intrinsic constant line**:

~~~text
Q(s,beta) = twoBoundaryOrderedSchurCoefficient(s,beta)

0 <= Q(s,beta) < 1/2

(1 - 2 Q(s,beta)) * ||f - Pi_const f||^2
  <= sum_{tagged one-link e} ||f - P_e f||^2.
~~~

The coefficient is strictly positive on the existing two-boundary loss-contraction cutoff. The proof retains the exact target-first/source-second two-boundary ordered kernel, including the one-point-supported cross-boundary block, and introduces no link-count or volume factor into the coefficient.

**Next theorem seam:** the right-hand side above is still the **unnormalized sum over all tagged one-link residuals**. The next unit must convert the two-sided one-link sweep to a **volume-safe grouped twelve-color sweep** and compare its path loss with the conventional 1/12 twelve-spatial residual energy. Once a positive conventional twelve-color Poincare coefficient is available on the physical right-boundary sector, the existing receiver already gives a positive finite-volume physical transfer gap.

A complete thermodynamic-limit and continuum four-dimensional Yang--Mills existence and mass-gap theorem is **not yet established** in this repository.

## Authority checkpoint — 2026-10-01 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing baseline | 22bfe27324e374242aad7bc402a224769306a22b — merged PR #4971 |
| #4971 validated exact PR head | cf43f174d76451400bb10301c6cb2549be0118b6 |
| #4971 validation | PR Lean Fast Check 36784485909: completed / success; matching exact-head receipt: success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md) · [Lean modules at the #4971 theorem snapshot](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic)

The default branch main is **not** theorem authority. README / ROADMAP on main are documentation mirrors only. A docs-only merge can advance a branch pointer without advancing the theorem-bearing baseline.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts and actual build diagnostics;
5. history / conversation memory.

## What is now closed

| Layer | Status through #4971 |
| --- | --- |
| Exact beta-zero physical transfer gap | Proved: gap at beta = 0 is exactly 1 |
| Actual cyclic source-update geometry and bounded representatives | Proved |
| Real source-fixed leakage coefficient and exact ordered RMS envelope | Proved in #4935--#4936 |
| Actual same-boundary terminal recurrence and Schur feedback | Proved in #4937 |
| Fixed-color geometric loss, zero-tail and renewal contraction | Proved in #4938--#4940 |
| All-right mixed-color relative Poincare | Proved in #4941--#4942 |
| Volume-free six-color grouped relative frame | Proved in #4943 |
| Retained-boundary physical-gap receiver | Proved conditionally in #4944; #4945 identifies the retained projection with the Doob/coarse projection |
| Two-boundary ordered Schur kernel on Sum Link Link | Proved in #4946 |
| Genuine left and two-sided one-link projections | Proved in #4947 |
| Variance-sensitive cross-boundary L2 estimate | Proved in #4948--#4954 |
| Concrete source-invariant target mean and source-fiber variance | Proved in #4955--#4958 |
| Exact one-link stationarity and endpoint-swap global transport | Proved in #4959--#4960 |
| Target variance to genuine target residual | Proved in #4961 |
| Source variance to genuine left leakage | Proved in #4962 |
| Genuine cross-boundary one-step L2 influence | Proved in #4963 |
| Actual left/right source-update cross leakage | Proved in #4964 |
| Exact diagonal support of cross block | Proved in #4965 |
| Four-orientation actual two-sided leakage with exact ordered block kernel | Proved in #4966 |
| Two-sided cyclic forcing budget | Proved in #4967 |
| Static original/terminal recurrence and two-boundary Schur feedback | Proved in #4968 |
| Strict full-sweep path-loss contraction on all joint L2 | Proved in #4969 |
| Full-sweep fixed space = intrinsic constant line; convergence to its orthogonal projection | Proved in #4970 |
| All-L2 two-sided relative Poincare with coefficient 1 - 2Q | Proved in #4971 |
| Volume-safe tagged-link to conventional 1/12 twelve-color bridge | **Open next seam** |
| Positive-beta finite-volume physical transfer gap from the new two-sided route | **Not yet closed** |
| Thermodynamic limit and continuum OS / Wightman construction | Downstream open |

## 1. Quantitative two-boundary objects

Let

~~~text
P_e       = genuine joint one-link conditional expectation
            on a tagged right/left link e in Sum Link Link

B         = orthogonal projection onto the intrinsic joint constant line

K(t,s)    = twoBoundaryOrderedKernel(target=t, source=s)

Q(s,beta) = twoBoundaryOrderedSchurCoefficient(s,beta)

eta(s,beta)
          = (Q / (1-Q))^2.
~~~

The two-boundary kernel has four blocks:

- right to right: the exact ordered same-boundary leakage coefficient;
- left to left: its endpoint-swap conjugate;
- left to right and right to left: the genuine cross-boundary coefficient;
- the cross blocks retain the exact one-point support: off the matching spatial-link diagonal the leakage is exactly zero.

This support is why the two-boundary Schur row/column bound remains volume-independent.

On the existing loss-contraction cutoff,

~~~text
0 <= Q < 1/2
0 <= eta < 1.
~~~

## 2. Cross-boundary L2 influence is now a genuine projection theorem

PRs #4948--#4963 close the former cross-boundary analytic seam without substituting a bounded-test/TV theorem for an arbitrary L2 statement.

The chain is:

~~~text
mutual Harnack control
  -> variance-sensitive mean-difference estimate
  -> actual kernel-section fiber law
  -> source-invariant concrete target mean
  -> exact iid factor-two cancellation
  -> source-fiber target-mean variance
  -> current source/target sections
  -> exact one-link stationarity
  -> endpoint-swap joint transport
  -> genuine target residual
  -> genuine left leakage
  -> actual cross-boundary L2 influence.
~~~

The resulting actual bounded-representative estimate has the unchanged cross coefficient:

~~~text
||P_R,target f - P_L,source(P_R,target f)||^2
  <= c_cross(beta)^2 * ||f - P_R,target f||^2
~~~

for the source-invariant representative required by the construction. PRs #4964--#4966 convert this to actual source updates, preserve the off-diagonal zero support, and assemble the four boundary orientations into the exact two-boundary ordered kernel.

No arbitrary factor two, link-count factor or volume factor is inserted in this chain.

## 3. Actual two-sided recurrence and geometric decay

PR #4967 supplies the bounded-core cyclic forcing telescope for the genuine two-sided one-link family.

PR #4968 defines the first-sweep local profile O and the second-sweep terminal profile T, classifies the actual suffix/prefix trajectory and proves

~~~text
T(target)
  <= sum_source K(target,source) * O(source)
   + sum_source K(target,source) * T(source).
~~~

The existing finite Schur theorem then gives

~~~text
(1-Q)^2 * sum T^2
  <= Q^2 * sum O^2.
~~~

PR #4969 shrinks to a positive, volume/rank-independent interval with Q < 1/2 and defines

~~~text
eta = (Q/(1-Q))^2 < 1.
~~~

For the actual complete tagged one-link sweep S,

~~~text
pathLoss(S f) <= eta * pathLoss(f)
~~~

first on the bounded concrete core and then on **all genuine joint L2** by density and closedness. Iterated path loss decays geometrically.

## 4. Full-sweep limit is the intrinsic constant line

PR #4970 identifies the common fixed space of all genuine right/left one-link projections.

The right half uses the already-proved all-right retained geometry. The left half is transported through the exact endpoint-swap L2 isometry. Mutual absolute continuity with pair Haar and the qualitative fst/snd boundary-collapse theorem then force simultaneous right/left fixed vectors to be a.e. constant.

Thus

~~~text
(forall tagged e, P_e f = f)
  <-> f belongs to the intrinsic joint constant line.
~~~

The converse is also proved. Therefore the complete full sweep has exactly that fixed space.

Let Pi_const denote the orthogonal projection onto the intrinsic joint constant line. Pi_const absorbs every tagged one-link projection and the full sweep. Combining this with #4969 gives

~~~text
S^n f -> Pi_const f
~~~

in the genuine joint L2 norm for every f.

## 5. All-L2 two-sided relative Poincare — #4971

PR #4971 extends the actual source-update forcing inequality from the dense bounded concrete core to **all joint L2** by a closed-set argument, with the same K(target,source).

For any duplicate-free tagged-link trajectory it proves

~~~text
(1-Q)^2 * pathLoss
  <= sum_e ||f - P_e f||^2.
~~~

For the canonical complete sweep, exact Pythagoras relative to Pi_const and the renewal tail give

~~~text
(1-eta) * ||f - Pi_const f||^2
  <= pathLoss.
~~~

Using the exact identity

~~~text
(1-Q)^2 * (1-eta) = 1 - 2Q,
~~~

the current theorem is

~~~text
(1 - 2Q) * ||f - Pi_const f||^2
  <= sum_e ||f - P_e f||^2.
~~~

The theorem also proves

~~~text
0 < 1 - 2Q
~~~

on the same #4969 cutoff.

This is the strongest current volume-independent coercivity statement in the new two-sided one-link route.

Source: [two-sided relative Poincare](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare.lean).

## 6. Why the positive-beta physical gap is not yet claimed

The #4971 right-hand side is

~~~text
sum over every tagged spatial link e of ||f - P_e f||^2.
~~~

It is **not** the conventional twelve-color energy

~~~text
E12(f) = (1/12) * sum_{12 spatial colors c} ||f - B_c f||^2.
~~~

A naive termwise bound from one-link residuals to their color residual and then summing over all links would introduce a color-class cardinality factor, hence a volume-dependent constant. That is not acceptable for the target volume-uniform gap.

The next proof must therefore preserve ordered sweep geometry and group links by the twelve spatial colors.

The required design is:

1. choose a duplicate-free complete tagged-link order grouped into the six right colors and six left colors;
2. identify each color group with the existing fixed-color one-link sweep;
3. use the nested-block path-loss theorem to charge a whole color-group path loss to one color residual, coefficient one;
4. transport the two-sided recurrence / loss contraction / constant-line convergence to this grouped order, or prove the needed order-independent version;
5. obtain a positive coefficient kappa12(s,beta) such that

~~~text
kappa12 * ||f - Pi_const f||^2
  <= conventional twelve-spatial residual energy.
~~~

On the physical top-orthogonal right-boundary sector, the existing theorem

periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_transferGap

then gives

~~~text
3 * kappa12 / 4 <= physical transfer gap
~~~

for 0 < kappa12 <= 1/2.

The exact beta-zero theorem gap_0 = 1 remains a separate stronger endpoint result.

## 7. Relation to the earlier all-right route

PRs #4941--#4943 already prove a volume-free all-right six-color relative frame. PR #4944 routes it to the physical gap under a retained-boundary contraction premise, and #4945 identifies the retained projection with the coarse/Doob projection.

That route left a separate contraction parameter rho to be supplied. The later two-sided route was built to remove that retained-boundary fixed-space seam by driving the complete right/left dynamics to the intrinsic constant line.

The current two-sided route has now reached relative Poincare coercivity, but its final normalization is still one-link rather than twelve-color. The two routes therefore meet at the next grouped-color bridge.

## 8. Existing physical receiver

The conventional twelve-color residual energy and its physical receiver are already formalized.

On a right-boundary lift, the six left-color residuals vanish exactly, so

~~~text
E12(R u) = (1/2) * E6(u).
~~~

A positive conventional twelve-spatial Poincare coefficient kappa on the physical top-orthogonal sector implies

~~~text
3*kappa/4 <= physical transfer gap.
~~~

Source: [twelve-spatial Poincare receiver](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean).

## 9. Lean / CI continuation notes

Recent repairs reinforce several stable Lean 4 rules for this repository:

- Do not use recursive congr on huge measure/variance terms. Prove the function equality separately with funext and lift it with one congrArg.
- Avoid giant broad rw or simp calls across dependent measure expressions. Use local definitions, typed intermediate equalities and calc chains.
- Keep source/target index orientation explicit. The physical transpose and the ordered kernel are target-first/source-second where stated.
- Treat a.e. equality as a.e. equality. Transport it with the exact measure-preserving / absolute-continuity API instead of evaluating arbitrary L2 representatives pointwise.
- Import the smallest required module. Generated local instance names can collide when two large import lanes are combined.
- Prefer pinned mathlib APIs such as lintegral_eq_zero_of_ae_eq_zero and direct variance_zero over simp guessing.
- For dense-core extensions, prove the desired inequality defines a closed subset and use the already-proved bounded-core density.
- Do not rerun expensive strict Lean checks after docs-only changes. For theorem changes, validate the exact PR head and inspect the actual build diagnostics as well as the receipt.

## 10. Restart sequence

Freshly observe formal/real-hilbert-uniform-coercive-strong-limit before continuing.

The theorem checkpoint documented here is:

~~~text
22bfe27324e374242aad7bc402a224769306a22b
merged PR #4971
~~~

The immediate continuation should start from:

- [#4971 two-sided relative Poincare](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare.lean)
- [#4970 constant-line convergence](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedConstantLineConvergence.lean)
- [#4969 loss contraction](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedLossContraction.lean)
- [#4968 terminal recurrence](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedOrderedTerminalRecurrence.lean)
- [#4943 grouped one-boundary frame machinery](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialGroupedLinkSweep.lean)
- [generic nested-block path-loss theorem](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/RealHilbertNestedBlockProjectionSweepPathLoss.lean)
- [existing twelve-color physical receiver](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean)

Do not restart the old #4932 frontier. The real norm conversion, physical-envelope construction, actual two-sided recurrence, strict loss contraction, fixed-space identification and all-L2 relative Poincare are already closed.

The current route is:

~~~text
CLOSED:
cross-boundary L2 influence
  -> exact two-boundary ordered kernel
  -> actual cyclic recurrence
  -> Schur feedback
  -> strict all-L2 loss contraction
  -> constant-line convergence
  -> all-L2 relative Poincare

NEXT:
volume-safe grouped twelve-color bridge

THEN:
positive conventional E12 Poincare
  -> existing physical transfer-gap receiver
  -> positive-beta finite-volume gap

LATER:
thermodynamic limit
  -> continuum OS reconstruction
  -> Hamiltonian / vacuum-sector gap
  -> Wightman reconstruction.
~~~
