# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-20 JST**.

Authoritative theorem-carrier branch:

    formal/real-hilbert-uniform-coercive-strong-limit

Exact theorem-bearing baseline for this refresh:

    e56ea50823fb70d6fb6f50e33ae79ea2a9d9ac01

This is the merge commit of PR #4575:

    Iterate response-controlled random-scan recurrence

This ROADMAP update is documentation-only. If it merges before another theorem PR, the branch pointer will advance while the theorem-bearing mathematical baseline remains the merge above.

Authority order:

    1. exact current GitHub theorem-carrier SHA
    2. formal Lean theorem artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

`main` is not theorem authority when histories differ.

---

# Current dependency graph

    A. FINITE PERIODIC WILSON / OS ROOT                         [INTEGRATED]
       -> compact SU(N) finite lattice
       -> reflection positivity / OS carriers
       -> one-slab transfer / ground-state architecture

    B. CONTINUOUS ONE-LINK LAW + LOCAL GEOMETRY                 [INTEGRATED]
       -> normalized one-link law
       -> measurable heat-bath reinsertion
       -> stationarity / represented-source cancellation
       -> active-neighbor degree <= 18
       -> C5 exceptional geometry

    C. EXACT KERNEL-SECTION / COVARIANCE MECHANICS              [INTEGRATED]
       -> conditional expectation identities
       -> L2 projection / fluctuation
       -> deterministic/random-scan telescopes
       -> finite covariance resolvent

    D. FIXED-VOLUME RANDOM-SCAN ERGODIC ROUTE                   [INTEGRATED]
       -> complete-block Doeblin contraction
       -> exact block/step bridge
       -> covariance remainder vanishes at M=n*L_H
                                                                 [#4547-#4548]

    E. COARSE TAGGED FIXED-RIGHT RESPONSE ROUTE                 [INTEGRATED]
       -> eligible pullback resolvent
       -> exact volume-growing row coefficient
       -> auxiliary unscanned response
       -> represented fixed-right finite-step/asymptotic response
       -> transport back to actual source-aligned remote forcing
                                                                 [#4551-#4558]

    F. GENUINE LOCAL EXPONENTIAL THEORY                         [INTEGRATED]
       -> W_center=s^baseL1Distance
       -> rho_s=18*eta(beta)*s^2
       -> weighted local row/column
       -> K_local^d W <= rho_s^d W
       -> G_local,M W <= (1-rho_s)^(-1) W
                                                                 [#4559-#4560]

    G. FIXED-TARGET WEIGHTED PHYSICAL ENVELOPE                  [INTEGRATED]
       -> local + target pin + actual remote residual
       -> absorb local/pin terms into weight bookkeeping
       -> weighted response-bootstrap interfaces
       -> variation-scaled one-link heat-bath propagation
       -> fixed-target physical tagged carrier
                                                                 [#4563-#4569]

    H. REMOTE RESIDUAL / RESPONSE LINEARIZATION                 [INTEGRATED]
       -> uniform remote certificate isolated as an interface only
       -> weighted random-scan superposition
       -> remote residual <= exp(16 beta) * fixed-right response
       -> response profile R defines configuration-independent K_R
       -> actual fixed-target envelope <= K_R
                                                                 [#4570-#4573]

    I. RESPONSE-CONTROLLED RANDOM-SCAN DYNAMICS                 [INTEGRATED]
       -> actual one-step left variation propagated by K_R
       -> right-boundary source forcing tracked separately
       -> v_(n+1)=Q_R v_n
       -> accumulated source discrepancy d_n
       -> finite-step left variation <= v_n
       -> finite-step boundary discrepancy <= d_n
                                                                 [#4574-#4575]

    J. SELF-CONSISTENT FIXED-RIGHT RESPONSE CLOSURE             [OPEN NOW]
       -> normalize d_(n+1)=d_n+forcing(v_n)
       -> explicit finite sum for d_n
       -> stationary finite-step response inequality using K_R
       -> weighted norm estimate for Q_R
       -> terminal discrepancy control
       -> asymptotic self-consistent response inequality
       -> solve for weighted response profile R

    K. ACTUAL REMOTE WEIGHTED COEFFICIENT                       [OPEN]
       -> apply #4572 to solved response profile
       -> derive concrete volume-independent kappa_s(beta,s)
       -> prove
            18*eta(beta)*s^2 + eta(beta) + kappa_s < 1
          in a nonempty parameter regime
       -> instantiate #4570 certificate interface

    L. STRICT WEIGHTED PHYSICAL INFLUENCE / SPATIAL DECAY       [OPEN]
       -> full weighted subinvariance
       -> source-to-target response decay
       -> terminal kernel-section base-L1 covariance decay

    M. UNIFORM REMOTE RESIDUAL / PHYSICAL SWEEP GATE            [OPEN]
       -> cubic shell summability
       -> volume-uniform remote residual
       -> strict physical sweep contraction

    N. PHYSICAL POINCARE / COERCIVITY                            [OPEN]

    O. UNIFORM FINITE-VOLUME TRANSFER / HAMILTONIAN GAP          [OPEN]

    P. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                  [OPEN]

    Q. CLAY-LEVEL EXISTENCE + MASS GAP                           [OPEN]

---

# Phase 0 — Authority and proof discipline

**Status: integrated and permanent.**

For theorem-bearing work:

    fresh-fetch theorem-carrier
      -> lock exact canonical SHA
      -> inspect full Lean files and imported interfaces
      -> formulate one mathematically coherent theorem unit
      -> push and fresh-observe current PR head
      -> follow CI for that exact head
      -> if head changes, discard the old CI authority
      -> repair Lean/API/syntax errors without weakening
      -> require completed/success on exact current head
      -> require exact-head CI receipt success
      -> merge with expected_head_sha
      -> fresh-fetch theorem-carrier again.

A stale run attached to an older PR head is not CI authority for a moved PR.

Queued/in-progress CI is not GREEN.

No new `sorry`, `admit`, axioms, hidden constants, hypothesis weakening, theorem weakening, or semantic broadening may replace proof.

---

# Phase 1 — Finite Wilson / OS root

**Status: integrated.**

The repository contains the finite periodic compact-`SU(N)` Wilson model, reflection-positive structures, one-slab transfer architecture, nonnegative ground-state framework, and downstream coercivity/spectral interfaces.

Boundary:

    finite Wilson / OS infrastructure
      != completed continuum Yang--Mills existence theorem.

---

# Phase 2 — Continuous one-link law and local geometry

**Status: integrated.**

The continuous one-link law is normalized and measurable; the repository contains one-link heat-bath reinsertion, stationarity/properness machinery, represented-source cancellation, and the physical C5/local-neighbor geometry.

The volume-independent active-neighbor degree and base-L1 locality are the geometric input for the genuine local Harnack kernel.

The dense distinct-fiber tagged carrier remains a valid finite-volume upper-bound mechanism, but not the final sparse spatial carrier.

---

# Phase 3 — Exact kernel-section covariance mechanics

**Status: integrated.**

The one-link kernel section is identified with the relevant conditional expectation. The repository contains the associated `L2` projection/fluctuation identities, covariance self-adjointness, one-link Dirichlet identities, deterministic-schedule telescopes, and restricted-random-scan covariance resolvents.

Permanent boundary:

    finite covariance resolvent
      != spatial covariance decay.

---

# Phase 4 — Fixed-volume block/step covariance remainder

**Status: CLOSED through #4547-#4548.**

PR #4547 proves the complete-block/original-step identity

    P_block^n f
      = P_scan^(n * L_H) f.

PR #4548 combines this with fixed-volume Doeblin convergence and proves

    Cov_mu(F, P_scan^(n * L_H) G) -> 0.

The covariance remainder is therefore closed at fixed finite volume.

Boundary:

    fixed-volume covariance-remainder vanishing
      != volume-uniform spatial covariance decay.

---

# Phase 5 — Coarse tagged fixed-right response

**Status: integrated through #4558.**

PRs #4551-#4557 build the eligible-coordinate pullback and fixed-right response resolvent.

The exact physical eligible-row coefficient includes

    (card(Link)-1) * DistinctFiberOffFiberInfluence(beta),

which records the fixed-volume obstruction explicitly.

PR #4558 transports the asymptotic fixed-right bound back to the actual source-aligned remote residual while retaining its real C5 support.

Result:

    useful finite-volume response machinery
    but not a uniform spatial contraction mechanism.

---

# Phase 6 — Exponentially weighted genuine local Harnack theory

**Status: CLOSED through #4560.**

Define

    W_center(x)
      := s ^ baseL1Distance(center,x),

with `s >= 1`.

PR #4559 proves

    K_local W
      <= rho_s W,

with

    rho_s
      := 18 * eta(beta) * s^2.

PR #4560 proves

    K_local^d W
      <= rho_s^d W

and, if

    rho_s < 1,

    G_local,M W
      <= (1-rho_s)^(-1) W.

This is the reusable volume-independent local Green mechanism.

---

# Phase 7 — Fixed-target weighted local/pin/remote decomposition

**Status: integrated through #4565.**

The actual fixed-target envelope is decomposed into

    genuine local Harnack contribution
      + distinguished-target pin
      + actual source-aligned remote residual.

The distinguished-target pin contributes an additional `eta(beta)` to the later full weighted coefficient.

The corresponding local/pin terms are now explicitly compatible with exponential weighting.

---

# Phase 8 — Weighted response bootstrap and variation propagation

**Status: integrated through #4569.**

PR #4566 lifts the fixed-target decomposition into a weighted response-bootstrap interface.

PR #4567 scales the physical influence bound by an arbitrary nonnegative variation profile.

PR #4568 transports that variation through the actual one-link heat-bath update.

PR #4569 packages the resulting fixed-target physical structure into a tagged carrier usable by random-scan algebra.

These theorems preserve the actual fixed-target law structure and do not identify the old coarse left-left carrier with the desired physical spatial kernel.

---

# Phase 9 — Uniform remote certificate interface

**Status: integrated through #4570, but certificate existence remains open.**

PR #4570 defines the interface

    actual weighted remote residual
      <= kappa * W.

If such a `kappa` is supplied, the full weighted coefficient becomes

    c_s
      = 18 * eta(beta) * s^2
        + eta(beta)
        + kappa.

It proves the downstream algebraic consequences, including weighted kernel/resolvent bootstrap under `c_s < 1`.

Important boundary:

    certificate interface
      != derivation of kappa.

---

# Phase 10 — Weighted superposition and remote-response linearization

**Status: CLOSED through #4572.**

PR #4571 establishes the weighted superposition needed to move target-dependent weights into variation profiles.

PR #4572 proves that if `R(target,source)` bounds the actual fixed-right target-ratio response, then on remote targets

    actual remote influence
      <= exp(16 * beta) * R(target,source),

and therefore

    actual weighted remote residual
      <= exp(16 * beta)
         * weighted_mass(R).

This is the key carrier-free bridge from fixed-right response to the actual remote residual.

It uses no terminal covariance decay, physical sweep contraction, Poincare/coercivity, or mass-gap input.

---

# Phase 11 — Response-controlled physical kernel

**Status: CLOSED through #4573.**

For a nonnegative fixed-right response profile `R`, define the response-controlled kernel `K_R` by the physical cases:

    diagonal:
      0

    C5/local exceptional:
      eta(beta)

    remote:
      exp(16 * beta) * R(target,source).

PR #4573 proves that the actual configuration-dependent fixed-target envelope is pointwise dominated by `K_R`.

It then transports this domination to the actual bounded-test and arbitrary-variation one-link heat-bath estimates.

Conceptual transition:

    actual update
      -> response-controlled physical kernel K_R

replaces the old use of the coarse all-to-all left-left carrier as the spatial recurrence.

Open point:

    R is still an input profile;
    it has not yet been constructed self-consistently.

---

# Phase 12 — One-step response-controlled random scan

**Status: CLOSED through #4574.**

PR #4574 proves that one actual restricted-random-scan step propagates left variation through `K_R`.

Schematically,

    v_next = Q_R v.

It separately defines the represented right-source forcing

    CrossBoundaryRandomScanSourceForcing(source,v).

This separation is structural: the dense left-left block of the old augmented tagged carrier does not enter the physical left-variation recurrence.

---

# Phase 13 — Finite-step response-controlled recurrence

**Status: CLOSED through #4575.**

Define

    v_0 = variation
    v_(n+1) = Q_R v_n.

PR #4575 proves that every actual `n`-step restricted-random-scan observable has left-fiber variation bounded by `v_n`.

For the represented right-boundary source, define

    d_0 = 0

and

    d_(n+1)
      = card(Link)^(-1)
        * sum_fiber [
            d_n
            + CrossBoundaryBoundedTestMajorant(beta,fiber,source)
              * v_n(fiber)
          ].

PR #4575 proves that two random-scan orbits with different represented right-boundary source values differ pointwise by at most `d_n`.

The coarse tagged carrier is used only to justify the right-source affine identity. Its volume-growing left-left block is not used in the recurrence that propagates spatial variation.

---

# Phase 14 — Normalize the source-discrepancy recurrence

**Status: OPEN — next coherent theorem unit.**

Because the spatial-link finite type is nonempty, the averaging term should simplify exactly to

    d_(n+1)
      = d_n
        + CrossBoundaryRandomScanSourceForcing(source,v_n).

Formal goals:

1. prove positivity/nonzeroness of

       card(PeriodicHypercubicEvenSpatialSliceLink H);

2. normalize the averaged discrepancy step;

3. prove the finite-sum identity

       d_n
         = sum_{j < n}
             CrossBoundaryRandomScanSourceForcing(source,v_j).

This removes avoidable averaging syntax before the stationary-response closure.

---

# Phase 15 — Stationary fixed-right response through K_R

**Status: OPEN — immediate analytic frontier.**

Replace the older coarse left-left finite-step response transport with the response-controlled recurrence.

Desired schematic theorem:

    actual fixed-right response
      <= accumulated_source_forcing(v_0,...,v_(n-1))
         + terminal_n_step_discrepancy.

The left profile must remain

    v_j = Q_R^j v_0,

not an iterate of the dense tagged carrier.

The terminal term should then be controlled or sent to zero under a strict weighted condition on `K_R`.

---

# Phase 16 — Self-consistent weighted response inequality

**Status: OPEN — central closure problem.**

Since the remote part of `K_R` itself contains `R`,

    K_R(remote)
      = exp(16 * beta) * R,

the closure is self-consistent.

The target is a weighted scalar/profile inequality such as

    M_R
      <= A(beta,s)
         + B(beta,s) * M_R,

where

    M_R
      := sup/source-normalized weighted mass of R,

and

    B(beta,s) < 1.

Then

    M_R
      <= A(beta,s) / (1-B(beta,s)).

The proof must derive this from the actual fixed-right law-level response and the response-controlled finite-step recurrence.

Do **not** close this phase by:

    * assuming the final response bound;
    * assuming the final remote certificate;
    * reverting to the coarse all-to-all left-left coefficient;
    * using terminal covariance decay;
    * importing a physical contraction, Poincare/coercivity, or mass gap.

---

# Phase 17 — Derive the actual remote coefficient

**Status: OPEN AFTER PHASE 16.**

Feed the solved response profile into #4572:

    weighted remote residual
      <= exp(16 * beta) * weighted_mass(R).

This should produce an explicit volume-independent

    kappa_s(beta,s).

Then instantiate the #4570 interface and prove a nonempty regime satisfying

    18 * eta(beta) * s^2
      + eta(beta)
      + kappa_s(beta,s)
      < 1.

This is the first point at which strict full weighted physical subinvariance is authorized.

---

# Phase 18 — Strict weighted physical influence and spatial decay

**Status: OPEN AFTER PHASE 17.**

From the strict coefficient derive:

    full weighted physical influence
      <= c_s W,

with

    c_s < 1.

Then obtain volume-independent source-to-target response/resolvent decay.

The target is a genuine sparse physical spatial mechanism, with no return to the dense tagged carrier.

---

# Phase 19 — Terminal kernel-section base-L1 covariance decay

**Status: OPEN DOWNSTREAM.**

Combine:

    source-singleton terminal variation
      + fixed-volume covariance-remainder closure (#4548)
      + strict weighted physical influence
      + exact kernel-section covariance mechanics.

Target:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^baseL1Distance(target,source),

uniformly in periodic volume, with

    C >= 0,
    0 <= q < 1.

---

# Phase 20 — Uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Use cubic base-L1 shell summability:

    terminal covariance decay
      -> terminal response decay
      -> volume-uniform remote residual
      -> strict physical sweep contraction.

Directionality is permanent:

    covariance decay
      -> uniform remote residual,

not the reverse.

---

# Phase 21 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After a volume-independent strict physical sweep estimate:

    physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

The required coercive constant must remain uniform in volume.

---

# Phase 22 — Uniform finite-volume transfer/Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

Target: a positive spectral lower bound uniform over the finite periodic volumes used in the limiting construction.

A fixed-volume spectral gap that collapses with volume is insufficient.

---

# Phase 23 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap, the program still requires:

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

Existing auxiliary/scalar continuum lanes remain infrastructure, not substitutes for the full gauge-field construction.

---

# Phase 24 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The repository should therefore be read as a rigorous formalization program with substantial finite-volume and analytic infrastructure, not as an already completed Clay solution.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline PR #4575:

    1. prove spatial-link cardinality is nonzero in the exact local context;

    2. normalize
         CrossBoundaryRandomScanSourceDiscrepancyStep
       into
         discrepancy + CrossBoundaryRandomScanSourceForcing;

    3. derive
         d_n = sum_{j<n} forcing(v_j);

    4. rebuild the stationary fixed-right finite-step response theorem
       using v_j = Q_R^j v_0 rather than the coarse left-left carrier;

    5. identify a weighted norm M_R for the actual response profile R;

    6. prove a strict weighted estimate for Q_R in terms of M_R;

    7. control the terminal n-step discrepancy and pass n -> infinity;

    8. derive a self-consistent inequality
         M_R <= A + B*M_R;

    9. prove B < 1 on a nonempty parameter regime and solve for M_R;

    10. use #4572 to obtain the actual volume-independent kappa_s;

    11. instantiate #4570 and prove
          18*eta(beta)*s^2 + eta(beta) + kappa_s < 1;

    12. derive strict weighted physical influence and spatial response decay;

    13. combine with #4548 to obtain terminal base-L1 covariance decay;

    14. run the cubic-shell / uniform-remote-residual pipeline;

    15. close physical sweep contraction, Poincare/coercivity,
        and the uniform finite-volume spectral gap;

    16. only then advance the thermodynamic/continuum Yang--Mills carrier
        and the Clay-level statement.

---

# Current conceptual transition

    #4547-#4548
      fixed-volume covariance remainder closed

    #4551-#4558
      coarse tagged fixed-right response route
      + explicit fixed-volume obstruction
      + transport back to actual remote forcing

    #4559-#4560
      genuine local exponential weighted Schur/resolvent theory

    #4563-#4569
      actual fixed-target local/pin/remote decomposition
      -> weighted response bootstrap
      -> variation-scaled heat-bath propagation

    #4570
      remote-certificate interface only

    #4571-#4572
      weighted superposition
      -> actual remote residual linearized through fixed-right response

    #4573
      response profile R
      -> response-controlled physical kernel K_R

    #4574
      one actual random-scan step
      -> left variation propagated by K_R
      + right-source forcing isolated

    #4575
      v_(n+1)=Q_R v_n
      + finite-step accumulated right-source discrepancy d_n

    current frontier
      actual stationary fixed-right response
      -> self-consistent weighted inequality for R
      -> explicit volume-independent kappa_s
      -> strict full weighted physical subinvariance.

---

# Permanent semantic boundaries

    finite-volume theorem != continuum theorem
    fixed-volume ergodicity != volume-uniform physical contraction
    random-scan mixing != spatial correlation decay
    covariance identity != covariance decay
    covariance decay != mass gap
    one-link conditional expectation != full Gibbs-law identification
    coarse tagged carrier != actual sparse physical carrier
    local weighted resolvent != remote weighted closure
    fixed-right response profile input != self-consistent construction of that profile
    response-controlled kernel K_R != proof of a bound for R
    uniform remote certificate != derivation of its coefficient
    exact weighted decomposition != strict absorption
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

These boundaries are part of the formal theorem architecture, not editorial caveats.
