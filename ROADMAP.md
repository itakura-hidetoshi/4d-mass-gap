# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-19 JST**.

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this refresh is:

    7184acd5f19fc5dc1d2e4b5f6774e7c3958ea805

This is the merge commit of PR #4513:

    Telescope restricted random-scan covariance through finite resolvent

This ROADMAP update is documentation-only. After its merge, the branch pointer will move, but the theorem-bearing mathematical baseline remains #4513 until a later theorem PR lands.

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
       -> periodic active graph / base-L1 geometry

    D. FIXED-RIGHT RESPONSE / CROSS-RATIO                        [INTEGRATED]
       -> target-ratio response
       -> targetwise worst-case majorants
       -> cardinality-free finite summation
       -> generic Doob bounded-test bridge

    E. ACTUAL REMOTE CONDITIONAL INFLUENCE                       [INTEGRATED #4464-#4469]
       -> model-specific SU(N) Doob instantiation
       -> actual bounded-test influence <= worst-case majorant
       -> source-summed remote column
       -> concrete remote residual kernel

    F. PHYSICAL LOCAL + REMOTE ENVELOPE                          [INTEGRATED #4470-#4478]
       -> active Harnack + remote residual
       -> source-aligned residual
       -> physical envelope kernel
       -> finite-volume residual maximum
       -> finite-volume sweep contraction under strict gate

    G. UNIFORM RESIDUAL REDUCTION                                [INTEGRATED #4479-#4494]
       -> uniform remote-residual certificate
       -> two-step terminal envelope
       -> terminal covariance normal form
       -> crossing denominator floor
       -> base-L1 shell geometry
       -> cubic shell summability
       -> covariance-decay predicate => uniform rho

    H. REMOTE KERNEL-SECTION CONDITIONAL EXPECTATION             [INTEGRATED #4495-#4506]
       -> actual one-link conditional law
       -> L2 projection
       -> covariance self-adjointness
       -> fluctuation decomposition
       -> idempotence / annihilation
       -> one-link covariance Dirichlet identity

    I. COVARIANCE TELESCOPES                                     [INTEGRATED #4507-#4513]
       -> deterministic schedule telescope
       -> local variation decrement
       -> tagged schedule propagation
       -> restricted random-scan Dirichlet identity
       -> finite iterate transport
       -> finite resolvent profile
       -> covariance remainder <= variation/resolvent pairing

    J. KERNEL-SECTION SPATIAL COVARIANCE DECAY                   [OPEN NOW]
       -> derive distance-sensitive resolvent / Green control
       -> prove base-L1 exponential terminal covariance decay

    K. UNIFORM PHYSICAL SWEEP / COERCIVITY                       [OPEN NEXT]
       -> explicit uniform rho
       -> strict physical column gate
       -> volume-independent full-sweep contraction
       -> Poincare / coercivity

    L. UNIFORM FINITE-VOLUME PHYSICAL GAP                        [OPEN]
       -> transfer/Hamiltonian spectral lower bound

    M. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                  [OPEN]
       -> same-root limiting state / OS carrier
       -> sufficiently rich Yang--Mills field/state

    N. CLAY-LEVEL EXISTENCE + MASS GAP                           [OPEN]

---

# Phase 0 — Authority and proof discipline

**Status: integrated and permanent.**

For theorem-bearing work:

    fresh-fetch theorem-carrier
    -> lock exact canonical SHA
    -> inspect exact Lean interfaces
    -> state one mathematically coherent theorem unit
    -> run exact-head CI
    -> fix the first genuine Lean error without weakening statements
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

# Phase 2 — Continuous one-link reference law and C5 geometry

**Status: integrated.**

The repository contains the exact normalized continuous one-link reference law, measurable conditional kernel, full-configuration heat-bath reinsertion, stationarity, and C5 geometry.

Key uniform local facts:

    active spatial plaquette-neighbor degree <= 18
    C5 exceptional set cardinality <= 20

The old dense distinct-fiber carrier remains available as a coarse bound but is not identified with the sparse physical carrier.

---

# Phase 3 — Fixed-right response and targetwise cross-ratio control

**Status: integrated through #4460.**

The fixed-right response lane now includes:

    target-ratio response
    -> target-indexed SU(N) tuples
    -> actual remote vacuum cross-ratio bound
    -> cardinality-free logarithmic influence linearization
    -> targetwise sSup worst-case majorant
    -> source-summed worst-case remote column
    -> generic Doob bounded-test comparison

The worst-case majorant is nonnegative and bounded by 2; no supremum attainment is assumed.

---

# Phase 4 — Actual model-specific remote conditional influence

**Status: integrated through #4464, #4467, #4469.**

The former normalization frontier is closed.

For geometrically remote target/source pairs, the actual normalized one-link conditional-law bounded-test difference is bounded by the targetwise worst-case cross-ratio influence majorant.

The remote source column is then summed without a remote-cardinality multiplier and packaged as a concrete nonnegative residual kernel.

Boundary:

    fixed-right response != actual influence

remains conceptually important, but the required bridge between them is now proved rather than assumed.

---

# Phase 5 — Physical local-plus-remote envelope

**Status: integrated through #4470-#4478.**

The actual physical source-update influence is split into:

    local intrinsic active-neighbor Harnack term
    + remote vacuum residual.

The source-aligned remote residual vanishes on the diagonal and active neighbors and equals the worst-case cross-ratio majorant on the remote complement.

The physical left influence envelope kernel is now explicit. Its column is bounded by:

    18 * eta(beta) + remoteResidualMaximum(H, A).

The exact finite-volume residual maximum and corresponding reciprocal random-scan contraction are formalized.

Boundary: this is still a finite-volume coefficient; uniform smallness in `H` is not yet established.

---

# Phase 6 — Uniform remote residual certificate

**Status: integrated through #4479-#4483.**

The uniformity problem is isolated as:

    RemoteResidualUniformBound(N, hN, beta, hbeta, rho).

Given such a nonnegative `rho`, the existing theorem transports it into a volume-independent physical envelope coefficient and full-sweep contraction.

The remote residual is reduced to:

    explicit two-step transport coefficient
    + uniform two-step terminal mass.

Thus the only nonlocal part of `rho` is the terminal correlation tail.

---

# Phase 7 — Terminal geometry and shell summability

**Status: integrated through #4484-#4494.**

The terminal problem now has a canonical spatial base-`L1` distance. The source-aligned remote shell satisfies the volume-independent polynomial bound:

    shellCard(r) <= 3 * (2*r + 1)^3.

The cubic shell majorant times `q^r` is summable for every:

    0 <= q < 1.

Therefore the shell route does not require an artificial graph-growth condition such as `18*q < 1`.

The theorem chain now proves:

    kernel-section covariance base-L1 decay
      -> terminal response base-L1 decay
      -> uniform terminal shell mass
      -> RemoteResidualUniformBound
      -> uniform physical full-sweep contraction.

All arrows except the first are already formalized.

---

# Phase 8 — Exact terminal covariance normal form

**Status: integrated through #4487 and #4489.**

The exact two-step terminal response is written as one covariance under the fixed-`k` ground-state kernel-section law divided by the source crossing-ratio expectation.

The denominator satisfies:

    crossingExpectation >= exp(-2 * beta),

so:

    terminalResponseAbs
      <= exp(2 * beta) * |kernelSectionCovariance|.

The denominator is therefore no longer an obstruction.

---

# Phase 9 — Remote kernel-section one-link conditional expectation

**Status: integrated through #4495-#4501.**

For remote target/source geometry, the actual one-link kernel-section heat-bath update is identified with conditional expectation onto the off-fiber sigma-algebra.

This yields:

    actual projection =a.e. condExp(offFiber)
    -> one-link stationarity
    -> `MemLp 2` preservation
    -> covariance self-adjointness.

No ordinary Gibbs-law identification is used.

---

# Phase 10 — One-link fluctuation and Dirichlet structure

**Status: integrated through #4502-#4506.**

Writing:

    P = one-link projection
    Q = I - P,

the repository proves:

    covariance symmetry for Q
    projection idempotence a.e.
    P(Qf) = 0 a.e.
    covariance orthogonal decomposition
    one-link covariance Dirichlet identity.

These are exact finite-volume `L2` statements under the remote kernel-section law.

---

# Phase 11 — Deterministic covariance telescope

**Status: integrated through #4507-#4510.**

Covariance is telescoped along finite deterministic one-link schedules. The one-link decrement is bounded by products of local fiber-variation bounds, and those bounds are propagated by the existing tagged variation machinery.

This gives the first direct bridge from conditional-expectation covariance algebra to quantitative variation transport.

---

# Phase 12 — Restricted random-scan covariance Dirichlet identity

**Status: integrated through #4511.**

The deterministic schedule layer is averaged over physical scan targets to obtain the restricted random-scan covariance decrement identity.

The normalization is by the number of physical spatial links, not by the full tagged carrier cardinality.

---

# Phase 13 — Finite restricted-scan iterate transport

**Status: integrated through #4512.**

Finite physical restricted-scan expectation iterates preserve the analytic hypotheses required by the covariance argument and inherit the tagged variation propagation bound.

In particular, the `m`-step observable variation is bounded by the `m`-step tagged restricted-scan variation iterate.

---

# Phase 14 — Finite resolvent covariance telescope

**Status: integrated through #4513.**

Define the normalized finite restricted-scan resolvent profile:

    R_M(v)(e)
      = card(Link)^(-1) * sum_{m < M} Q^m(v)(e).

The exact finite covariance telescope gives:

    Cov(F,G) - Cov(F, P_scan^M G)
      = sum of the first M covariance decrements.

The quantitative theorem then proves:

    |Cov(F,G) - Cov(F, P_scan^M G)|
      <= sum_e variationF(e) * R_M(variationG)(e).

This is the current theorem-bearing frontier.

Boundary: #4513 is a finite-`M` estimate. It does not prove that `P_scan^M G` converges to a constant or that the remainder vanishes.

---

# Phase 15 — Spatially weighted kernel-section covariance decay

**Status: OPEN NOW.**

The isolated analytic target from #4493 is:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^(baseL1Distance(target, source))

uniformly in periodic volume, with:

    C >= 0,
    0 <= q < 1.

The new #4513 finite-resolvent telescope supplies the covariance-comparison mechanism, but a distance-sensitive estimate is still needed.

The next work should preserve spatial information instead of collapsing immediately to a total variation norm. The literal dense C5 carrier has column size proportional to `card(Link)`, so it cannot supply the required uniform decay by itself.

Required substeps:

    1. prove explicit variation profiles for the source crossing observable;
    2. prove explicit variation profiles for the two-step terminal observable;
    3. connect actual fixed-target kernel-section updates to a sparse/distance-sensitive
       physical influence carrier without replacing the law by a different
       source-aligned law;
    4. derive a spatial Green/resolvent bound from the covariance telescope;
    5. convert graph propagation to the canonical base-L1 distance;
    6. prove the #4493 covariance-decay predicate.

---

# Phase 16 — Close the uniform physical residual and sweep gate

**Status: OPEN NEXT.**

Once Phase 15 supplies the covariance decay predicate, #4494 already yields an explicit volume-uniform remote residual scalar:

    rho = exp(16*beta) *
      (twoStepTransportCoefficient(beta)
       + cubicBaseL1TerminalShellMass).

The existing envelope theorem then reduces physical contraction to a strict scalar gate.

The source-aligned physical route is organized around:

    18 * eta(beta) + rho < 1.

The older C5 exceptional-set route can produce a `20 * eta + rho` interface under its own hypotheses. These constants belong to different decompositions and must not be conflated.

---

# Phase 17 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After a uniform physical sweep contraction is available, the next target is a volume-independent variance/coercivity estimate for the actual physical finite-volume carrier.

Schematic route:

    strict physical response control
    -> block / conditional variance estimate
    -> Poincare / coercivity
    -> transfer-sector control.

---

# Phase 18 — Uniform finite-volume transfer/Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

The required output is a scale-independent positive constant producing a physical spectral lower bound uniform over the finite periodic volumes used in the limiting construction.

A positive gap with a constant that collapses with volume is insufficient.

---

# Phase 19 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap is established, the remaining program includes:

    compatible limiting physical states
    -> same-root OS/Wightman carrier
    -> limiting semigroup / Hamiltonian
    -> sufficiently rich nontrivial 4D Yang--Mills field/state
    -> spectral lower bound above the vacuum.

The existing scalar continuum OS lane is same-root infrastructure, not a substitute for the full gauge-field construction.

---

# Phase 20 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The present repository contains a large formal proof spine and a sharply localized continuous-`SU(N)` analytic frontier, but the final claim remains open until the spatial kernel-section covariance decay, uniform physical residual gate, coercivity, uniform finite-volume gap, and limiting field/state obligations are discharged.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4513:

    1. formalize source-crossing and terminal-observable variation profiles;

    2. build the fixed-target spatial influence / resolvent bridge needed by
       the exact kernel-section law used in the terminal covariance;

    3. derive a distance-sensitive finite-resolvent estimate from #4513;

    4. prove uniform base-L1 exponential decay of the exact terminal
       kernel-section covariance;

    5. invoke the existing cubic shell theorem to obtain uniform rho;

    6. close the strict physical envelope gate and full-sweep contraction;

    7. derive physical Poincare/coercivity;

    8. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

    9. advance the thermodynamic/continuum physical Yang--Mills carrier;

    10. only then close the Clay-level existence and mass-gap statement.

---

# Current conceptual transition

    #4464-#4469:
      actual remote SU(N) conditional influence and residual kernel

    #4470-#4478:
      physical sparse local-plus-remote envelope and finite-volume sweep

    #4479-#4494:
      uniform residual reduced to terminal covariance decay
      + denominator floor
      + cubic base-L1 shell geometry and summability

    #4495-#4506:
      remote kernel-section update becomes an L2 conditional-expectation
      projection with exact covariance/Dirichlet structure

    #4507-#4513:
      one-link Dirichlet structure telescoped through deterministic schedules
      and then through finite physical restricted random scan

    current frontier:
      turn the finite covariance resolvent into spatial base-L1 exponential
      decay without losing distance information or introducing a volume factor.
