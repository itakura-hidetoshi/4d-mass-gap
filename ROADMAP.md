# MGAP4D ROADMAP

## Authority checkpoint — 2026-10-01 JST

| Item | Value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique authoritative theorem-carrier | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing baseline | 22bfe27324e374242aad7bc402a224769306a22b |
| Latest theorem merge | PR #4971 — all-L2 two-sided relative Poincare |
| #4971 validated PR head | cf43f174d76451400bb10301c6cb2549be0118b6 |
| #4971 validation | PR Lean Fast Check 36784485909: completed / success; matching exact-head receipt: success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Overview](README.md)

main is not theorem authority. README / ROADMAP on main are documentation mirrors only. A docs-only merge can advance branch pointers without advancing the theorem-bearing baseline.

Authority order remains:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts plus actual build diagnostics;
5. history / memory.

## 0. Current frontier

The old #4932 frontier is completely obsolete.

The following chain is now formally closed:

~~~text
real source-fixed leakage coefficient
  -> exact ordered RMS envelope
  -> actual terminal recurrence
  -> fixed-color geometric loss / renewal
  -> all-right mixed-color relative frame

plus

genuine left one-link geometry
  -> variance-sensitive cross-boundary L2 comparison
  -> actual kernel-section target mean / variance
  -> exact source-fiber iid cancellation
  -> stationarity
  -> endpoint-swap global transport
  -> genuine target residual
  -> genuine left leakage
  -> actual cross-boundary one-step L2 influence
  -> exact diagonal cross support

then

four-orientation two-sided ordered kernel
  -> bounded-core cyclic forcing
  -> original/terminal profile recurrence
  -> two-boundary Schur feedback
  -> strict full-sweep loss contraction
  -> all-L2 extension
  -> fixed space = intrinsic constant line
  -> convergence to Pi_const
  -> all-L2 two-sided relative Poincare.
~~~

The current theorem is:

~~~text
Q(s,beta)
  = GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta

beta <= twoBoundaryOrderedLossContractionCutoff(s,hs)
hs : 8 < s
beta >= 0

0 <= Q < 1/2

(1 - 2Q) * ||f - Pi_const f||^2
  <= sum_e ||f - P_e f||^2
~~~

for every genuine joint L2 vector f, where e ranges over the tagged right/left one-link carrier.

The coefficient 1 - 2Q is strictly positive and volume-independent.

**The only immediate analytic normalization seam is now the right-hand side.** It is an unnormalized sum over all links, not the conventional 1/12 twelve-spatial color energy. A naive termwise link-to-color comparison would introduce a volume-dependent color-class cardinality factor and is therefore not an acceptable final bridge.

The next proof unit must be a **grouped twelve-color sweep bridge**.

## 1. Current notation and exact domains

Suppress the physical parameters H, N, hN, beta, hbeta when unambiguous.

~~~text
P_e
  = genuine joint one-link CondExpL2 for a tagged link
    e : Sum Link Link

B_c^R
  = genuine right-boundary color-block CondExpL2

B_c^L
  = genuine left-boundary color-block CondExpL2

B
  = Pi_const
  = orthogonal projection onto the intrinsic joint constant line

K(target,source)
  = twoBoundaryOrderedKernel

Q
  = twoBoundaryOrderedSchurCoefficient(s,beta)

eta
  = twoBoundaryOrderedLossRatio(s,beta)
  = (Q/(1-Q))^2

S
  = complete canonical tagged one-link sweep

loss(f)
  = exact path loss of one complete tagged one-link sweep.
~~~

On the #4969 loss-contraction cutoff:

~~~text
0 <= Q < 1/2
0 <= eta < 1
0 < 1 - 2Q.
~~~

The common fixed space is exact:

~~~text
(forall e, P_e f = f)
  <-> f in intrinsic joint constant line

S f = f
  <-> f in intrinsic joint constant line.
~~~

The full sweep converges:

~~~text
S^n f -> B f.
~~~

These statements hold on the genuine joint L2 carrier, not only on the bounded concrete core.

## 2. Closed theorem chain

### 2.1 Same-boundary ordered leakage and all-right relative frame — #4935--#4945

PR #4935 converts the finite ENNReal squared leakage estimate to a real norm estimate while preserving the exact iid half factor.

PR #4936 factors the coefficient into the exact ordered pin-free kernel entry and a scalar RMS multiplier. Row/column bounds are proved in their correct orientation; no symmetry assumption is introduced. It constructs a volume/rank-independent Schur coefficient.

PR #4937 assembles the actual bounded-core original/terminal recurrence.

PR #4938 proves fixed-color geometric loss decay with

~~~text
eta = (Q/(1-Q))^2 < 1.
~~~

PR #4939 identifies the actual fixed-color sweep limit and closes strict renewal.

PR #4940 extends the ordered defect margin to the full genuine joint L2 carrier.

PRs #4941--#4942 build the all-right mixed-color path-loss and relative-Poincare theory with an explicit retained left-boundary projection.

PR #4943 groups links by the six right spatial colors and derives a volume-free six-color relative frame. This is the key precedent for the next twelve-color grouped bridge.

PR #4944 sends that relative frame to the physical-gap receiver under a retained-boundary contraction hypothesis.

PR #4945 proves that the literal retained projection is the same orthogonal projection as the earlier coarse/Doob presentation. It does not itself prove the missing contraction constant.

### 2.2 Two-boundary ordered kernel and cross-boundary analytic closure — #4946--#4963

PR #4946 defines the two-boundary target-first block kernel on Sum Link Link:

- same-boundary blocks: exact ordered same-boundary coefficient;
- cross blocks: existing one-point-supported C5 majorant.

Every row and every column is bounded by the sum of the same-boundary coefficient and the cross coefficient, with no link-count factor. The finite Schur theorem produces the two-boundary coefficient Q.

PR #4947 adds the literal left one-link retained sigma-algebra, left CondExpL2, idempotence/symmetry and the common right/left tagged-link family.

PR #4948 proves the generic variance-sensitive L2 mean-difference estimate from mutual Harnack bounds.

PR #4949 specializes it to the actual cross-boundary conditional fibers.

PR #4950 proves endpoint-swap symmetry of the genuine ground-state joint law.

PR #4951 lifts swap to an L2 linear-isometry equivalence and proves exact right/left one-link projection conjugacy.

PR #4952 proves the generic exact independent-pair factor-two cancellation:

~~~text
pair mean-difference energy
  = 2 * variance

pair estimate
  <= 2 * c^2 * E[V]

therefore

variance
  <= c^2 * E[V].
~~~

PR #4953 identifies the historical reference fiber with the actual source-updated kernel-section fiber.

PR #4954 rewrites the cross-boundary L2 comparison entirely in actual kernel-section laws.

PR #4955 inserts a bounded source-invariant concrete joint observable and builds the actual target mean.

PR #4956 integrates the pairwise estimate over the source iid pair and obtains source-fiber target-mean variance control with the unchanged c_cross(beta)^2 coefficient.

PR #4957 identifies the source profile as the source-coordinate section of one current target-mean observable.

PR #4958 performs the same current-section identification for the target variance.

PR #4959 proves full-background measurability and exact one-link stationarity return.

PR #4960 outer-globalizes this through exact vacuum/kernel-section disintegration and endpoint swap.

PR #4961 identifies the ordinary target-variance average with the existing canonical target fiber variance and bounds it by the genuine target one-link CondExpL2 residual.

PR #4962 identifies the source-coordinate variance with the genuine left-source leakage norm.

PR #4963 combines both sides into the genuine cross-boundary one-step L2 influence theorem.

At this point the analytic cross-boundary seam is closed.

### 2.3 Actual two-sided updates and exact support — #4964--#4966

PR #4964 shows endpoint swap preserves the bounded concrete core, builds a left-source-invariant representative for an actual left one-link update, and applies #4963 to that actual update.

PR #4965 preserves the exact C5 support after lifting to L2:

~~~text
source != target
  -> genuine cross-boundary leakage = 0.
~~~

For source = target the existing c_cross(beta) coefficient is retained. Hence the actual cross leakage is controlled by the literal one-point-supported cross majorant used by #4946.

PR #4966 mirrors same-boundary and cross-boundary estimates through endpoint swap and case-splits the four right/left source/target orientations. The resulting actual source-update theorem uses exactly

~~~text
twoBoundaryOrderedKernel(target,source).
~~~

It then feeds the generic Hilbert source-residual identity.

### 2.4 Two-sided recurrence, contraction and fixed space — #4967--#4970

PR #4967 builds a preserved-domain cyclic forcing telescope on the bounded concrete core for arbitrary finite tagged-link trajectories.

PR #4968 defines the first-sweep profile O and second-sweep profile T and proves

~~~text
T(target)
  <= sum_source K(target,source) O(source)
   + sum_source K(target,source) T(source).
~~~

The existing Schur estimate yields

~~~text
(1-Q)^2 * sum T^2
  <= Q^2 * sum O^2.
~~~

PR #4969 chooses a positive volume/rank-independent interval with Q < 1/2 and proves

~~~text
loss(S f) <= eta * loss(f)
eta = (Q/(1-Q))^2 < 1.
~~~

The inequality is extended from the bounded concrete core to all joint L2 by density and closedness. Iterated losses satisfy geometric decay.

PR #4970 proves the fixed-space theorem:

~~~text
all tagged one-link projections fix f
  <-> f lies in the intrinsic joint constant line.
~~~

The proof uses exact all-right retained geometry, endpoint swap, pair-Haar fst/snd measurability and the qualitative boundary-collapse theorem.

The orthogonal projection Pi_const absorbs each tagged one-link projection and the complete sweep, and

~~~text
S^n f -> Pi_const f
~~~

for every joint L2 vector.

### 2.5 All-L2 relative Poincare — #4971

PR #4971 first extends the two-sided source-update forcing estimate from the bounded concrete core to all joint L2 by closedness.

For any duplicate-free tagged-link order:

~~~text
(1-Q)^2 * pathLoss
  <= sum_e ||f - P_e f||^2.
~~~

For the canonical complete sweep, exact Pythagoras and #4970 convergence give

~~~text
(1-eta) * ||f - Pi_const f||^2
  <= pathLoss.
~~~

The exact scalar identity

~~~text
(1-Q)^2 * (1-eta) = 1 - 2Q
~~~

then yields

~~~text
(1 - 2Q) * ||f - Pi_const f||^2
  <= sum_e ||f - P_e f||^2.
~~~

No bounded-core premise remains in this theorem.

Source:
[two-sided relative Poincare](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare.lean).

## 3. The remaining finite-volume seam

### The obstruction

The #4971 RHS is an unnormalized link sum.

For one link e in color c, one has a residual domination of the form

~~~text
||f - P_e f||
  <= ||f - B_c f||.
~~~

But summing this termwise over every link in color c produces the size of that color class. That factor grows with the spatial volume.

Therefore the next proof must **not** finish #4971 by a direct termwise sum.

### The correct route

Reuse ordered sweep geometry and the existing grouped-sweep / nested-block machinery.

The next unit should:

1. define a complete duplicate-free tagged-link list grouped into twelve color blocks:
   - six right-boundary colors;
   - six left-boundary colors;

2. prove exact completeness and Nodup, preserving the internal canonical order of each color fiber;

3. identify each group operator with the existing fixed-color one-link sweep for that boundary/color;

4. use the generic nested-block theorem

~~~text
pathLoss(one-link sweep inside color c)
  <= ||x - B_c x||^2
~~~

with coefficient one;

5. transport the two-sided cyclic recurrence / loss contraction / constant-line convergence to the grouped complete order, or prove the required order-independent version of the recurrence;

6. use only the fixed number twelve of color groups when telescoping between group inputs;

7. derive a positive, volume-independent conventional twelve-color Poincare coefficient kappa12:

~~~text
kappa12(s,beta) * ||f - Pi_const f||^2
  <= E12(f),

E12(f)
  = (1/12) * sum_{12 colors c} ||f - B_c f||^2.
~~~

A fixed numerical factor depending on twelve colors is acceptable; a factor depending on the number of links is not.

## 4. Existing physical receiver after the grouped bridge

The conventional twelve-color energy is already defined and the physical receiver is already proved.

For a physical right-boundary lift R u:

~~~text
E12(R u) = (1/2) * E6(u)
~~~

because all six left-color residuals vanish exactly.

The theorem

periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_transferGap

proves:

~~~text
0 <= kappa <= 1/2

kappa * ||x||^2 <= E12(R(U x))
for every physical top-orthogonal x

=> 3*kappa/4 <= physical transfer gap.
~~~

Hence once the grouped bridge provides a positive volume-independent kappa12 on the required physical sector, the positive-beta finite-volume transfer gap follows from existing code.

This is distinct from the exact beta-zero result gap_0 = 1.

Source:
[twelve-spatial receiver](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean).

## 5. Planned theorem units

### G1. Two-sided grouped twelve-color tagged-link order — NEXT

Construct the right-six plus left-six grouped tagged-link list.

Completion criteria:

- complete enumeration of Sum Link Link;
- duplicate-free;
- each color fiber appears exactly once;
- group-local order matches the existing canonical fixed-color list;
- no commutativity assumption.

### G2. Grouped two-sided recurrence / order transport — NEXT

Either generalize #4968--#4970 from the current canonical univ.toList order to an arbitrary complete Nodup order, or instantiate their proof chain directly on the grouped order.

Keep exactly the same target-first/source-second K and Q.

Completion criteria:

~~~text
loss_grouped(S_grouped f)
  <= eta * loss_grouped(f)

S_grouped^n f -> Pi_const f.
~~~

No change to Q or eta.

### G3. Volume-safe twelve-color path-loss charge — NEXT

Apply the fixed-color nested-block theorem within each of the twelve groups:

~~~text
groupPathLoss_c(x)
  <= ||x - B_c x||^2.
~~~

Control the change of group inputs only with a fixed twelve-group argument, reusing the strategy of #4943 where possible.

Completion criteria: a volume-independent coefficient relating grouped total path loss to E12(f).

### G4. Conventional twelve-color Poincare — NEXT

Combine G2 and G3 to prove

~~~text
kappa12(s,beta) * ||f - Pi_const f||^2
  <= E12(f)
~~~

on the full genuine joint L2 carrier, or at minimum on the exact physical right-boundary top-orthogonal sector required by the receiver.

Prove:

~~~text
0 < kappa12
kappa12 <= 1/2
~~~

after shrinking if necessary. Do not introduce a lattice-size-dependent cutoff.

### G5. Positive-beta finite-volume physical transfer gap

Apply the already-proved receiver:

~~~text
3*kappa12/4 <= physical transfer gap.
~~~

Record the complete volume/rank-independent beta interval and all sector assumptions.

### G6. Thermodynamic limit — downstream

After a finite-volume gap is genuinely available:

- compatible finite-volume embeddings/restrictions;
- tightness / limiting vacuum state;
- transfer/semigroup compatibility;
- uniform persistence of the gap on the correct limiting carrier.

### G7. Continuum OS / Hamiltonian / Wightman construction — downstream

The later continuum program still requires:

- Euclidean field continuum limit;
- continuum OS axioms and reflection positivity;
- reconstruction of the physical Hilbert space;
- strongly continuous time translations;
- self-adjoint Hamiltonian;
- vacuum/sector identification;
- transfer-to-Hamiltonian-gap bridge;
- Wightman reconstruction.

A finite-volume gap alone is not the final continuum theorem.

## 6. Milestone ledger — #4933 through #4971

| PR | Classification | Contribution |
| --- | --- | --- |
| #4933 | Docs | README / ROADMAP checkpoint through #4932 |
| #4934 | Docs | Mirror #4933 docs to main |
| #4935 | Theorem | Real leakage norm coefficient; bounded-core cyclic forcing |
| #4936 | Theorem | Exact ordered RMS leakage envelope and uniform small-coupling Schur cutoff |
| #4937 | Theorem | Actual bounded-core terminal recurrence |
| #4938 | Theorem | Fixed-color geometric loss decay and renewal-tail bridge |
| #4939 | Theorem | Actual fixed-color sweep limit and strict renewal contraction |
| #4940 | Theorem | Full-joint-L2 ordered defect margin |
| #4941 | Theorem | All-right-link mixed-color sweep control |
| #4942 | Theorem | All-right relative Poincare to retained left boundary |
| #4943 | Theorem | Volume-free grouped six-color relative frame |
| #4944 | Theorem | Retained-boundary physical-gap receiver |
| #4945 | Theorem | Retained CondExp = coarse/Doob projection |
| #4946 | Theorem | Two-boundary ordered Schur block kernel |
| #4947 | Theorem | Genuine left and two-sided one-link projections |
| #4948 | Theorem | Variance-sensitive L2 mean difference from mutual Harnack |
| #4949 | Theorem | Cross-boundary conditional-fiber L2 specialization |
| #4950 | Theorem | Endpoint-swap symmetry of the ground-state joint law |
| #4951 | Theorem | Endpoint-swap L2 conjugacy of one-link projections |
| #4952 | Theorem | Exact iid factor-two cancellation |
| #4953 | Theorem | Reference fiber = updated kernel-section fiber |
| #4954 | Theorem | Actual kernel-section cross-boundary L2 control |
| #4955 | Theorem | Concrete source-invariant target means |
| #4956 | Theorem | Source-fiber target-mean variance control |
| #4957 | Theorem | Source profile = current target-mean section |
| #4958 | Theorem | Target variance = current source section |
| #4959 | Theorem | Full-background measurability and exact stationarity |
| #4960 | Theorem | Genuine-joint swap transport of target variance |
| #4961 | Theorem | Target variance -> genuine target residual |
| #4962 | Theorem | Source variance -> genuine left leakage |
| #4963 | Theorem | Genuine cross-boundary one-step L2 influence |
| #4964 | Theorem | Apply cross leakage to actual left source updates |
| #4965 | Theorem | Exact diagonal support of genuine cross leakage |
| #4966 | Theorem | Four-orientation actual two-sided leakage with exact block kernel |
| #4967 | Theorem | Bounded-core two-sided cyclic forcing budget |
| #4968 | Theorem | Actual two-sided terminal recurrence and Schur feedback |
| #4969 | Theorem | Strict two-sided full-sweep loss contraction on all L2 |
| #4970 | Theorem | Fixed space = constant line; full-sweep convergence |
| #4971 | Theorem | All-L2 two-sided relative Poincare with positive 1 - 2Q coefficient |

## 7. Validation evidence

Latest theorem-bearing baseline:

~~~text
22bfe27324e374242aad7bc402a224769306a22b
~~~

Latest validated theorem PR:

~~~text
PR #4971
exact head: cf43f174d76451400bb10301c6cb2549be0118b6
PR Lean Fast Check: 36784485909
status: completed / success
matching exact-head receipt: success
~~~

The validation is evidence that the stated Lean artifacts compile in the pinned environment. It is not a claim of independent mathematical review or completion of the continuum Yang--Mills theorem.

## 8. Lean 4 continuation notes

Recent theorem work produced several reusable rules.

### Avoid recursive congruence on huge analytic terms

In #4957, recursive congr on a large variance / measure expression exhausted heartbeats. The stable pattern is:

1. prove the underlying function equality with funext;
2. lift it one level using congrArg;
3. use a short calc chain.

Do not ask the elaborator to recursively decompose a giant measure expression.

### Avoid broad dependent rewriting

For large kernel / conditional-expectation terms:

- introduce typed local definitions;
- prove small intermediate equalities;
- use simpa only when possible;
- use explicit ContinuousLinearMap.comp_apply;
- avoid broad rw through dependent terms.

### Respect a.e. equality

Do not evaluate arbitrary L2 quotient representatives pointwise.

Use:

- Lp.ext;
- coeFn lemmas;
- measure-preserving pullback;
- absolute-continuity transport;
- kernel composition / stationarity;
- a.e. congruence.

### Keep coefficient orientation explicit

The two-boundary kernel is target-first/source-second where declared.

Do not infer symmetry from similar names. Row and column bounds must be invoked in their actual orientation.

### Preserve exact support

The cross block is one-point-supported. Do not replace it by an all-to-all c_cross matrix: that would manufacture a link-count loss.

### Import narrowly

Large import lanes may contain generated local-instance names that collide. #4970 required replacing an unnecessarily broad physical-kernel import with the smaller residual-kernel dependency. Import the smallest theorem module needed.

### Use pinned mathlib APIs

Examples from the recent chain:

- lintegral_eq_zero_of_ae_eq_zero;
- variance_zero directly rather than simp guessing;
- explicit measurable-kernel integral APIs;
- dense-core closed-set extension for all-L2 inequalities.

### Docs-only policy

README / ROADMAP-only changes do not justify another strict Lean build.

For docs mirrors:

- inspect only the docs diff and links;
- do not warm theorem caches unnecessarily;
- do not manufacture a theorem validation receipt;
- never merge the theorem branch wholesale into main.

## 9. Restart sequence

At the start of the next thread:

1. fresh-observe formal/real-hilbert-uniform-coercive-strong-limit;
2. classify any commits after 22bfe27324e374242aad7bc402a224769306a22b;
3. begin from #4971, not from the historical #4932 response chain;
4. inspect #4943 grouped-sweep machinery and the generic nested-block path-loss theorem;
5. construct the grouped right-six + left-six tagged-link order;
6. preserve the existing K, Q, eta and constant-line projection exactly;
7. derive the conventional twelve-color Poincare coefficient;
8. apply the existing twelve-spatial physical receiver.

Primary sources:

- [#4971 relative Poincare](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare.lean)
- [#4970 constant-line convergence](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedConstantLineConvergence.lean)
- [#4969 loss contraction](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedLossContraction.lean)
- [#4968 terminal recurrence](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedOrderedTerminalRecurrence.lean)
- [#4966 actual two-sided leakage](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedActualOneLinkLeakage.lean)
- [#4963 cross-boundary genuine one-step L2](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCrossBoundaryGenuineOneStepL2.lean)
- [#4943 grouped right-six sweep](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialGroupedLinkSweep.lean)
- [generic nested-block path loss](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/RealHilbertNestedBlockProjectionSweepPathLoss.lean)
- [twelve-spatial physical receiver](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/22bfe27324e374242aad7bc402a224769306a22b/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap.lean)

Current concise frontier:

~~~text
CLOSED:
all-L2 two-sided relative Poincare
with positive volume-independent coefficient 1 - 2Q

OPEN NEXT:
volume-safe grouped twelve-color normalization

THEN:
positive conventional E12 Poincare
  -> existing physical transfer-gap receiver
  -> positive-beta finite-volume gap

DOWNSTREAM:
thermodynamic limit
  -> continuum OS reconstruction
  -> Hamiltonian gap
  -> Wightman reconstruction.
~~~
