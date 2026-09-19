# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-19 JST**.

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this refresh is:

    550a84c972ac3c289d1b70ba7ec9c2beab0b3501

This is the merge commit of PR #4521:

    Propagate physical local Harnack influence in base-L1

This ROADMAP update is documentation-only. After its merge, the branch pointer will move, but the theorem-bearing mathematical baseline remains #4521 until a later theorem PR lands.

Authority order:

    1. exact current GitHub theorem-carrier SHA
    2. formal Lean theorem artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

`main` is not theorem authority when histories differ.

---

# Current dependency graph

    A. FINITE PERIODIC WILSON / OS ROOT                          [INTEGRATED]
       -> compact SU(N) finite lattice
       -> reflection positivity / OS carriers
       -> one-slab transfer and ground-state structure
       -> conditional-expectation / coercivity interfaces

    B. CONTINUOUS C5 ONE-LINK REFERENCE LAW                     [INTEGRATED]
       -> normalized fiber probability law
       -> measurable heat-bath kernel
       -> stationarity / properness
       -> represented-source cancellation

    C. LOCAL GEOMETRY                                            [INTEGRATED]
       -> intrinsic active-neighbor degree <= 18
       -> C5 exceptional set <= 20
       -> periodic active graph
       -> canonical link-base L1 geometry

    D. FIXED-RIGHT / CROSS-RATIO REMOTE CONTROL                 [INTEGRATED]
       -> target-ratio response
       -> targetwise worst-case majorants
       -> actual remote conditional influence
       -> concrete remote residual kernel

    E. PHYSICAL LOCAL + REMOTE ENVELOPE                          [INTEGRATED]
       -> active Harnack + remote residual
       -> source-aligned physical envelope
       -> finite-volume residual maximum
       -> finite-volume strict-gate sweep contraction

    F. UNIFORM REMOTE-RESIDUAL REDUCTION                         [INTEGRATED]
       -> two-step terminal envelope
       -> exact terminal covariance normal form
       -> crossing denominator floor
       -> cubic base-L1 shell bound
       -> covariance decay predicate => uniform residual rho

    G. EXACT KERNEL-SECTION L2 / COVARIANCE STRUCTURE             [INTEGRATED]
       -> remote one-link conditional expectation
       -> L2 projection / fluctuation
       -> covariance self-adjointness
       -> one-link covariance Dirichlet identity

    H. COVARIANCE TELESCOPES                                     [INTEGRATED]
       -> deterministic schedule telescope
       -> tagged variation propagation
       -> restricted random-scan covariance identity
       -> finite iterate transport
       -> finite resolvent covariance bound

    I. SOURCE-LOCALIZED TERMINAL RESOLVENT                        [INTEGRATED #4515]
       -> source crossing variation is singleton-supported
       -> two-step terminal variation profile
       -> finite covariance pairing collapses to one source entry

    J. DENSE-CARRIER SPATIAL OBSTRUCTION                          [INTEGRATED #4516]
       -> coarse off-fiber one-step profile is flat off target
       -> different base-L1 radii receive the same coarse coefficient
       -> dense carrier cannot be the final spatial-decay mechanism

    K. PLAQUETTE-LOCAL TO BASE-L1 BRIDGE                         [INTEGRATED #4518]
       -> one local step changes base-L1 distance by <= 2
       -> d-step local path changes distance by <= 2d
       -> distance >= 2D gives local path separation D

    L. SPARSE SINGLETON PROXY RESOLVENT                           [INTEGRATED #4519]
       -> singleton forcing
       -> separated finite-resolvent geometric tail
       -> useful Green-function model
       -> NOT identified with actual physical kernel

    M. ACTUAL PHYSICAL LOCAL HARNACK KERNEL                       [INTEGRATED #4520]
       -> local kernel supported exactly on active neighbors
       -> nonzero local edge => shared spatial plaquette
       -> physical envelope = local Harnack + remote residual
       -> column mass <= 18 * eta_local(beta)

    N. FIXED-TARGET EXACT PHYSICAL ENVELOPE                       [INTEGRATED #4517]
       -> C5-exceptional pair => Harnack coefficient
       -> C5-remote pair => target-specific actual remote residual
       -> law-level bounded-test domination
       -> no source-aligned identification assumed

    O. ACTUAL LOCAL BASE-L1 PROPAGATION                           [INTEGRATED #4521]
       -> local Harnack symmetry
       -> row mass = column mass
       -> K_local^d row mass <= rho_local^d
       -> nonzero K_local^d => base-L1 distance <= 2d
       -> distance >= 2D => K_local^d = 0 for d < D

    P. ACTUAL LOCAL HARNACK GREEN / RESOLVENT                     [OPEN NOW]
       -> sum local powers under rho_local < 1
       -> derive geometric base-L1 tail
       -> preserve exact physical coefficient eta_local

    Q. LOCAL + REMOTE PERTURBATION                               [OPEN NEXT]
       -> reorganize response through local Green operator
       -> retain exact remote residual as perturbation
       -> avoid assuming terminal covariance decay to prove remote control

    R. RANDOM-SCAN COVARIANCE REMAINDER                          [OPEN NEXT]
       -> control Cov(F, P_scan^M G)
       -> justify M -> infinity or an equivalent finite closure
       -> do not infer remainder vanishing from finite resolvent alone

    S. EXACT TERMINAL KERNEL-SECTION COVARIANCE DECAY             [OPEN]
       -> combine P + Q + R
       -> prove volume-uniform base-L1 exponential decay
       -> instantiate already-formalized #4493 predicate

    T. UNIFORM PHYSICAL RESIDUAL / SWEEP GATE                     [OPEN]
       -> cubic shell theorem gives uniform rho
       -> strict physical column gate
       -> volume-independent full-sweep contraction

    U. PHYSICAL POINCARE / COERCIVITY                             [OPEN]
       -> variance / coercivity estimate
       -> transfer-sector control

    V. UNIFORM FINITE-VOLUME PHYSICAL GAP                         [OPEN]
       -> scale-independent transfer/Hamiltonian spectral lower bound

    W. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                  [OPEN]
       -> compatible limiting states / OS carrier
       -> sufficiently rich 4D Yang--Mills field/state

    X. CLAY-LEVEL EXISTENCE + MASS GAP                            [OPEN]

---

# Phase 0 — Authority and proof discipline

**Status: integrated and permanent.**

For theorem-bearing work:

    fresh-fetch theorem-carrier
    -> lock exact canonical SHA
    -> inspect exact Lean interfaces
    -> state one mathematically coherent theorem unit
    -> run exact-head CI
    -> repair the first genuine Lean error without weakening statements
    -> inspect the whole changed proof when syntax/API structure is involved
    -> require completed/success on the exact head
    -> merge against the expected head
    -> fresh-fetch canonical again

Queued or in-progress CI is not GREEN.

No new `sorry`, `admit`, axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening may be introduced as a substitute for proof.

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: integrated.**

The finite periodic compact-`SU(N)` Wilson model, reflection-positive structures, one-slab transfer operators, nonnegative ground-state architecture, and downstream coercivity/spectral interfaces form the theorem root.

Boundary: this is not by itself a continuum Yang--Mills existence theorem.

---

# Phase 2 — Continuous one-link law and local C5 geometry

**Status: integrated.**

The repository contains the exact normalized continuous one-link law, measurable conditional kernel, full-configuration heat-bath reinsertion, stationarity, and C5 geometry.

Key volume-independent local facts:

    active spatial plaquette-neighbor degree <= 18
    C5 exceptional set cardinality <= 20.

The old dense distinct-fiber carrier remains a legitimate coarse upper bound, but it is not the actual sparse physical carrier.

---

# Phase 3 — Actual remote conditional influence

**Status: integrated through #4464-#4469.**

For geometrically remote target/source pairs, the normalized one-link bounded-test conditional-law response is controlled by a targetwise worst-case cross-ratio majorant.

The source column can be summed without introducing a remote-cardinality multiplier and is packaged as a concrete nonnegative remote residual.

This closes the old gap:

    fixed-right response
      -> actual remote conditional-law influence.

---

# Phase 4 — Physical local-plus-remote envelope

**Status: integrated through #4470-#4478.**

The actual physical source-update influence is split into:

    local intrinsic active-neighbor Harnack contribution
    + remote vacuum residual.

The resulting finite-volume physical envelope has a column coefficient schematically:

    18 * eta_local(beta) + remoteResidualMaximum(H, A).

Strictness gives finite-volume contraction.

Boundary: this is not yet volume-uniform because the remote maximum has not yet been quantitatively closed uniformly in `H`.

---

# Phase 5 — Uniform remote residual reduction

**Status: integrated through #4479-#4494.**

The remote uniformity problem is isolated in an explicit certificate.

The nonlocal part is reduced to a two-step terminal quantity, and the exact terminal response is normalized to a covariance under the fixed-`k` ground-state kernel-section law.

The crossing denominator obeys:

    crossingExpectation >= exp(-2 * beta),

hence:

    terminalResponseAbs
      <= exp(2 * beta) * |kernelSectionCovariance|.

The source-aligned remote base-`L1` shell satisfies:

    shellCard(r) <= 3 * (2*r + 1)^3.

The cubic shell majorant times `q^r` is summable for every `0 <= q < 1`.

Therefore:

    volume-uniform exponential terminal covariance decay
      -> uniform terminal shell mass
      -> uniform remote residual rho
      -> uniform physical sweep coefficient.

All arrows after the covariance-decay input are already formalized.

---

# Phase 6 — Exact kernel-section conditional expectation and L2 structure

**Status: integrated through #4495-#4506.**

For remote target/source geometry, the actual kernel-section one-link update is identified with conditional expectation onto the off-fiber sigma-algebra.

Consequences include:

    one-link stationarity
    MemLp 2 preservation
    covariance self-adjointness
    Q = I - P fluctuation structure
    projection idempotence
    P(Qf) = 0 a.e.
    covariance orthogonal decomposition
    one-link covariance Dirichlet identity.

No full Gibbs-law identification is assumed.

---

# Phase 7 — Deterministic and restricted-random-scan covariance telescopes

**Status: integrated through #4507-#4513.**

The one-link Dirichlet identity is telescoped first through deterministic schedules and then through restricted random scan.

The repository has a normalized finite restricted-scan resolvent profile:

    R_M(v)(e)
      = card(Link)^(-1) * sum_{m < M} Q^m(v)(e),

with a finite covariance estimate:

    |Cov(F,G) - Cov(F,P_scan^M G)|
      <= sum_e variationF(e) * R_M(variationG)(e).

Boundary:

    finite M
      != infinite resolvent
      != vanishing covariance remainder.

This distinction remains active at the current frontier.

---

# Phase 8 — Source-singleton terminal finite-resolvent reduction

**Status: integrated through #4515.**

The source crossing-ratio variation is now explicit and supported on exactly one physical source fiber:

    exp(2*beta) - exp(-2*beta)

at the source and zero elsewhere.

The actual two-step terminal target observable has an explicit propagated physical-left variation profile.

Therefore the generic #4513 resolvent pairing collapses exactly to one source coordinate of the terminal finite resolvent.

This is a major spatial localization step, but it remains finite-volume and finite-`M`.

---

# Phase 9 — Formal dense off-fiber obstruction

**Status: integrated through #4516.**

The current coarse distinct-fiber restricted-scan carrier is proved spatially flat off the target after one step.

Consequently, different off-target sources with different base-`L1` radii can receive the same coarse propagated value.

Interpretation:

    this is an obstruction of the carrier,
    not a no-go theorem for the exact physical covariance.

Development consequence:

> Do not attempt to prove spatial covariance decay by repeatedly sharpening the same distance-blind dense coefficient.

The route must separate genuinely local propagation from the remote vacuum residual.

---

# Phase 10 — Plaquette-local propagation versus base-L1 distance

**Status: integrated through #4518.**

One actual Wilson-plaquette-local step changes periodic link-base `L1` distance by at most two:

    local step => distance <= 2.

A chain/path of `d` such steps satisfies:

    endpoint distance <= 2*d.

Thus:

    2*D <= baseL1Distance(target, source)

implies singleton supports are separated by at least `D` plaquette-local propagation steps.

This supplies the exact geometry needed for finite-propagation-speed arguments.

---

# Phase 11 — Sparse Dobrushin singleton resolvent proxy

**Status: integrated through #4519.**

A singleton forcing profile is propagated through a sparse Dobrushin random-scan carrier.

Under that carrier's own strict threshold, base-`L1` separation produces a geometric finite-resolvent bound.

This theorem is useful as a model for the desired local Green estimate, but it is **not** the final physical theorem.

Permanent boundary:

    sparse Dobrushin proxy coefficient
      != physical background-update Harnack coefficient

unless an explicit theorem proves a relation.

---

# Phase 12 — Actual physical local Harnack kernel

**Status: integrated through #4520.**

The genuinely local part of the actual physical left influence envelope is now a first-class kernel:

    K_local(target, source)
      = eta_local(beta)  on intrinsic active neighbors
      = 0                otherwise.

Theorems now prove:

    K_local = 0 off active neighbors,

    K_local != 0
      -> active-neighbor relation
      -> shared spatial Wilson plaquette,

    PhysicalEnvelope
      = K_local + RemoteResidual,

and:

    columnMass(K_local) <= 18 * eta_local(beta).

The actual bounded-test physical one-link response is bounded by this same local kernel plus the unchanged remote residual.

---

# Phase 13 — Exact fixed-target physical envelope

**Status: integrated through #4517.**

The exact fixed-target kernel-section one-link law now has its own physical left-left envelope.

For an off-diagonal pair:

    C5-exceptional
      -> eta_local(beta),

    C5-remote
      -> target-specific actual remote residual.

This gives law-level bounded-test domination without replacing the fixed-target law by the source-aligned envelope.

Permanent boundary:

    fixed-target physical envelope
      != source-aligned physical envelope.

The distinction may only be removed by an explicit bridge theorem.

---

# Phase 14 — Actual local Harnack base-L1 propagation

**Status: integrated through #4521.**

The local Harnack kernel is symmetric. Therefore its row and column sums agree, and every row satisfies:

    rowMass(K_local) <= 18 * eta_local(beta).

Define:

    rho_local(beta) := 18 * eta_local(beta).

Recursive powers `K_local^d` are now formalized with:

    rowMass(K_local^d)
      <= rho_local(beta)^d.

The spatial support theorem is stronger:

    K_local^d(target, source) != 0
      -> baseL1Distance(target, source) <= 2*d.

Hence if:

    2*D <= baseL1Distance(target, source),

then every degree `d < D` vanishes exactly:

    K_local^d(target, source) = 0.

This is the present theorem-bearing frontier.

---

# Phase 15 — Sum the actual local powers into a Green/resolvent bound

**Status: OPEN NOW.**

The next coherent theorem unit is the actual local-Harnack analogue of the geometric proxy resolvent.

Assuming:

    rho_local(beta) < 1,

combine:

    exact vanishing for d < D
    + pointwise/row bound by rho_local^d

to obtain a finite and then geometric local resolvent tail.

Target schematic statement:

    2*D <= baseL1Distance(target, source)

      ->

    sum_{d < M} K_local^d(target, source)
      <= sum_{D <= d < M} rho_local^d
      <= rho_local^D / (1 - rho_local).

This theorem should stay entirely in the current continuous-vacuum import lane and should not import a legacy carrier merely to reuse an incompatible measurable-space instance.

---

# Phase 16 — Local Green operator plus exact remote perturbation

**Status: OPEN NEXT.**

The exact physical influence structure is:

    K_physical = K_local + R_remote.

The local Green operator alone does not control the full law.

The next abstract/model-specific bridge should reorganize an inequality of the form:

    w <= v + K_local^T w + R_remote^T w

into a statement controlled by the local Green operator:

    w <= G_local v + G_local(R_remote^T w) + remainder,

with all hypotheses explicit.

Required discipline:

    do not assume terminal covariance decay
      merely to prove the remote residual estimate
      that is later used to prove terminal covariance decay.

This is the principal non-circularity constraint of the current frontier.

---

# Phase 17 — Resolve the restricted-random-scan covariance remainder

**Status: OPEN NEXT.**

The finite telescope controls:

    Cov(F,G) - Cov(F,P_scan^M G),

not `Cov(F,G)` directly.

A valid closure therefore needs one of:

    P_scan^M G -> constant in a sufficiently strong sense,

or another theorem that controls:

    Cov(F,P_scan^M G)

uniformly and sends it to zero or absorbs it into a closed finite argument.

The current repository does not yet contain that result.

Permanent boundary:

    finite covariance resolvent
      != proof of ergodicity
      != vanishing covariance remainder.

---

# Phase 18 — Exact terminal kernel-section base-L1 covariance decay

**Status: OPEN AFTER PHASES 15-17.**

The target remains the predicate isolated earlier:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^(baseL1Distance(target, source))

uniformly in periodic volume, with:

    C >= 0,
    0 <= q < 1.

The expected proof now has a sharper architecture:

    source-singleton variation
      -> local Green finite propagation
      -> exact remote perturbation
      -> covariance-remainder closure
      -> base-L1 exponential terminal covariance decay.

The old dense distinct-fiber carrier is not part of this final spatial mechanism except as a coarse comparison/obstruction object.

---

# Phase 19 — Close uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Once Phase 18 is available, the already-integrated cubic shell theorem produces a volume-uniform remote residual scalar.

The physical source-aligned route then reduces contraction to a strict scalar gate of the form:

    18 * eta_local(beta) + rho_remote(beta) < 1.

The older `20 * eta + rho` C5-exceptional interface belongs to a different decomposition and must not be conflated with this 18-neighbor local-Harnack route.

---

# Phase 20 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After uniform physical sweep contraction, derive a volume-independent variance/coercivity estimate for the actual physical finite-volume carrier.

Schematic route:

    strict physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

---

# Phase 21 — Uniform finite-volume transfer/Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

The required output is a positive lower bound uniform over the finite periodic volumes used in the limiting construction.

A gap whose constant collapses with volume is insufficient.

---

# Phase 22 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap is established, the remaining program includes:

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

The existing scalar continuum OS lane is same-root infrastructure, not a substitute for the full gauge-field construction.

---

# Phase 23 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The repository now has a substantially more localized analytic frontier than at #4513: the local physical propagation mechanism is explicit and distance-sensitive. What remains is to close its interaction with the exact remote residual and the covariance remainder, then propagate the resulting terminal covariance decay through the already-built uniform-residual, contraction, coercivity, finite-gap, and continuum pipelines.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4521:

    1. define the finite local-Harnack resolvent from K_local^d;

    2. prove exact removal of degrees d < D from a base-L1 lower bound;

    3. sum the remaining powers geometrically under
         rho_local(beta) = 18 * eta_local(beta) < 1;

    4. package the resulting pointwise local Green/base-L1 tail theorem;

    5. build a local-plus-remote perturbation theorem using the exact
       decomposition PhysicalEnvelope = K_local + R_remote;

    6. instantiate the corresponding bridge for the fixed-target
       kernel-section law without identifying it with the source-aligned law;

    7. close or quantitatively absorb the finite restricted-random-scan
       covariance remainder;

    8. prove the exact terminal kernel-section covariance-decay predicate;

    9. invoke the existing cubic shell theorem to obtain uniform rho_remote;

    10. close the strict physical sweep gate;

    11. derive physical Poincare/coercivity;

    12. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

    13. advance the thermodynamic/continuum physical Yang--Mills carrier;

    14. only then close the Clay-level existence and mass-gap statement.

---

# Current conceptual transition

    #4513:
      finite restricted-random-scan covariance resolvent

    #4515:
      source variation becomes singleton-supported,
      collapsing the finite-resolvent pairing to one source entry

    #4516:
      coarse distinct-fiber propagation is formally shown
      to erase spatial radius information

    #4518:
      actual plaquette-local path length is connected to
      canonical periodic link-base L1 distance

    #4519:
      sparse singleton proxy demonstrates the geometric Green-tail mechanism

    #4520:
      actual physical local Harnack kernel is extracted from
      the exact local-plus-remote envelope

    #4517:
      exact fixed-target kernel-section law receives its own
      Harnack/remote physical envelope

    #4521:
      powers of the actual local Harnack kernel acquire
      volume-independent mass bounds and exact base-L1 finite propagation

    current frontier:
      sum those actual local powers into a spatial Green operator,
      perturb by the exact remote residual without circularity,
      and resolve the covariance remainder.
