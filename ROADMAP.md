# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-20 JST**.

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this refresh is:

    2fba0b625f39e581881bee1c2979b44c462bc62a

This is the merge commit of PR #4561:

    Isolate exponential weighted remote envelope column

This ROADMAP update is documentation-only. After its merge, the branch pointer may advance while the theorem-bearing mathematical baseline remains the latest theorem-bearing merge unless another theorem PR lands first.

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
       -> one-slab transfer / ground-state architecture

    B. CONTINUOUS ONE-LINK LAW + PHYSICAL LOCAL GEOMETRY        [INTEGRATED]
       -> normalized one-link law
       -> measurable heat-bath reinsertion
       -> stationarity / represented-source cancellation
       -> active-neighbor degree <= 18
       -> C5 exceptional geometry

    C. EXACT KERNEL-SECTION / COVARIANCE MECHANICS              [INTEGRATED]
       -> conditional expectation identities
       -> L2 projection / fluctuation
       -> deterministic and random-scan telescopes
       -> finite covariance resolvent

    D. FIXED-VOLUME RANDOM-SCAN ERGODIC ROUTE                   [INTEGRATED]
       -> Haar minorization
       -> complete-block Doeblin contraction
       -> stationary mean convergence
       -> exact block/step bridge
       -> covariance remainder vanishes at M=n*L_H
                                                                  [#4530-#4548]

    E. COARSE TAGGED ELIGIBLE-ROW RESOLVENT                     [INTEGRATED]
       -> eligible pullback resolvent
       -> exact row coefficient
       -> auxiliary unscanned response
       -> represented right-source bound
       -> fixed-right finite-step response
       -> asymptotic fixed-right response
                                                                  [#4551-#4557]

    F. ACTUAL PHYSICAL LOCAL / REMOTE BRIDGE                    [INTEGRATED]
       -> actual local Harnack kernel
       -> exact local + remote perturbation
       -> source-aligned remote residual
       -> asymptotic fixed-right bound transported back
                                                                  [through #4558]

    G. EXPONENTIAL LOCAL WEIGHTED THEORY                        [INTEGRATED]
       -> W_center(x)=s^baseL1Distance(center,x)
       -> weighted row/column <= rho_s W
       -> rho_s = 18*eta(beta)*s^2
       -> K_local^d W <= rho_s^d W
       -> G_local,M W <= (1-rho_s)^(-1) W
                                                                  [#4559-#4560]

    H. FULL PHYSICAL WEIGHTED COLUMN DECOMPOSITION              [INTEGRATED]
       -> C_full weighted column
          = local weighted column + actual remote weighted column
       -> local <= rho_s W(source)
       -> abstract absorption interface for remote coefficient
                                                                  [#4561]

    I. ACTUAL REMOTE WEIGHTED COEFFICIENT                       [OPEN NOW]
       -> derive concrete volume-independent kappa_s
       -> prove R_remote,weighted <= kappa_s W
       -> prove rho_s + kappa_s < 1 in a nonempty parameter regime
       -> no circular terminal-covariance input

    J. STRICT WEIGHTED PHYSICAL INFLUENCE / SPATIAL DECAY       [OPEN]
       -> full weighted subinvariance
       -> spatial response decay
       -> terminal kernel-section base-L1 covariance decay

    K. UNIFORM REMOTE RESIDUAL / PHYSICAL SWEEP GATE            [OPEN]
       -> cubic shell summability
       -> volume-uniform remote residual
       -> strict physical sweep contraction

    L. PHYSICAL POINCARE / COERCIVITY                           [OPEN]

    M. UNIFORM FINITE-VOLUME TRANSFER / HAMILTONIAN GAP         [OPEN]

    N. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                 [OPEN]

    O. CLAY-LEVEL EXISTENCE + MASS GAP                          [OPEN]

---

# Phase 0 — Authority and proof discipline

**Status: integrated and permanent.**

For theorem-bearing work:

    fresh-fetch theorem-carrier
    -> lock exact canonical SHA
    -> inspect exact Lean interfaces and full changed files
    -> state one mathematically coherent theorem unit
    -> push and fresh-observe PR current head
    -> query CI for that exact head
    -> if head moves, abandon the old run immediately
    -> repair genuine Lean/API/syntax errors without weakening
    -> require completed/success on the exact current head
    -> require exact-head CI receipt success
    -> merge against expected head SHA
    -> fresh-fetch theorem-carrier again.

A stale run attached to an older PR head is not CI authority for a moved PR.

Queued or in-progress CI is not GREEN.

No new `sorry`, `admit`, axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening may be introduced as substitutes for proof.

---

# Phase 1 — Finite Wilson / OS root

**Status: integrated.**

The finite periodic compact-`SU(N)` Wilson model, reflection-positive structures, one-slab transfer operators, nonnegative ground-state architecture, and downstream coercivity/spectral interfaces form the theorem root.

Boundary:

    finite Wilson / OS infrastructure
      != completed continuum Yang--Mills existence theorem.

---

# Phase 2 — Continuous one-link law and local geometry

**Status: integrated.**

The repository contains the normalized continuous one-link law, measurable heat-bath reinsertion, one-link stationarity/properness machinery, and the physical C5/local-neighbor geometry.

Key local facts include the volume-independent active-neighbor degree bound and the base-L1 locality needed by the genuine local Harnack kernel.

The old dense distinct-fiber tagged carrier remains a valid coarse upper-bound mechanism but is not the final sparse spatial carrier.

---

# Phase 3 — Exact kernel-section covariance mechanics

**Status: integrated.**

The exact kernel-section one-link update is identified with conditional expectation on the relevant off-fiber sigma-algebra. The repository contains the associated `L2` projection/fluctuation identities, covariance self-adjointness, one-link Dirichlet identities, deterministic schedule telescopes, and restricted-random-scan finite covariance resolvents.

Permanent boundary:

    finite covariance resolvent
      != spatial covariance decay.

---

# Phase 4 — Source localization and local/remote separation

**Status: integrated.**

The source crossing variation is singleton-supported.

The coarse distinct-fiber carrier is spatially flat off target, so repeated sharpening of that carrier cannot yield volume-uniform base-L1 decay.

The actual physical comparison is therefore separated into:

    genuine local Harnack propagation
      +
    actual remote physical forcing.

This is the structural split used by all later weighted arguments.

---

# Phase 5 — Actual local Harnack finite propagation and Green control

**Status: integrated.**

A nonzero local Harnack step changes periodic link-base L1 distance by at most two.

The actual local Harnack kernel has volume-independent row/column mass control. Its powers have exact finite propagation, and the finite local Green kernel inherits geometric spatial control under the local strictness condition.

The local part is therefore analytically understood without using the coarse all-to-all tagged carrier.

---

# Phase 6 — Weighted remote geometry and fixed-right bridge

**Status: integrated through #4558.**

The source-aligned actual remote residual is propagated through the local Green geometry rather than collapsed to a global L1 norm.

Earlier work connects this actual remote forcing to a fixed-right response profile.

PRs #4551-#4557 then develop an explicit restricted-random-scan resolvent for the coarse tagged carrier:

    eligible-coordinate pullback
      -> geometric eligible-total contraction
      -> auxiliary unscanned response
      -> represented right-source bound
      -> fixed-right finite-step response
      -> asymptotic fixed-right response.

PR #4553 computes the exact physical eligible row coefficient:

    (card(Link) - 1) * DistinctFiberOffFiberInfluence(beta).

This makes the limitation explicit: the coarse tagged criterion is fixed-volume and is not a uniform spatial contraction mechanism.

PR #4558 transports the asymptotic fixed-right response back to the actual source-aligned remote residual while retaining the exact C5 remote support.

Result:

    scan-depth dependence removed
    but volume-independent spatial decay still open.

---

# Phase 7 — Fixed-volume block/step bridge and covariance remainder

**Status: CLOSED through #4547-#4548.**

This phase was the main open item in the previous roadmap and is now complete.

PR #4547 proves the exact complete-block/original-step identity

    P_block^n f
      = P_scan^(n * L_H) f

under the established fixed-volume observable hypotheses.

PR #4548 combines this with the stationary Doeblin block limit and proves

    Cov_mu(F, P_scan^(n * L_H) G) -> 0.

Therefore the finite-volume covariance remainder is no longer an open dependency.

Important boundary:

    fixed-volume covariance-remainder vanishing
      != volume-uniform spatial covariance decay.

---

# Phase 8 — Exponentially weighted local Harnack row/column

**Status: CLOSED through #4559.**

Define

    W_center(x)
      := s ^ baseL1Distance(center,x),

with

    s >= 1.

Using the genuine active-neighbor carrier and the already-proved distance-step bound, PR #4559 proves

    sum_source
      K_local(target,source) * W_center(source)
      <=
      rho_s * W_center(target),

where

    rho_s
      := 18 * eta(beta) * s^2.

By symmetry, the same coefficient controls the weighted column.

This estimate is volume-independent.

If

    rho_s < 1,

the local carrier is strictly subinvariant in the exponential weight.

---

# Phase 9 — Iterated exponential local resolvent

**Status: CLOSED through #4560.**

PR #4560 iterates the weighted local inequality:

    K_local^d W
      <= rho_s^d W.

It also proves the finite local resolvent bound

    G_local,M W
      <= (1-rho_s)^(-1) W

uniformly in the resolvent depth `M`, under

    rho_s < 1.

This is the current reusable weighted local Green mechanism.

It uses no remote-response estimate, terminal covariance decay, physical sweep contraction, Poincare/coercivity, or mass-gap input.

---

# Phase 10 — Full physical weighted column decomposition

**Status: CLOSED through #4561.**

Define the actual source-aligned weighted remote residual column by

    R_remote,weighted(center,source)
      :=
    sum_target
      R_remote(source,target)
      * W_center(target).

PR #4561 proves the exact full-envelope decomposition

    sum_target
      C_full(target,source) * W_center(target)

      =

    sum_target
      K_local(target,source) * W_center(target)

      +

    R_remote,weighted(center,source).

The local term satisfies

    local weighted column
      <= rho_s * W_center(source).

No remote coefficient is assumed.

The formal absorption interface is:

    if
      R_remote,weighted(center,source)
        <= kappa_s * W_center(source),

    then
      full weighted column
        <= (rho_s + kappa_s) * W_center(source).

If additionally

    rho_s + kappa_s < 1,

the full physical envelope is strictly subinvariant in the exponential weight.

This theorem isolates the remaining analytic problem exactly.

---

# Phase 11 — Derive the actual remote weighted coefficient

**Status: OPEN NOW.**

This is the immediate theorem-development frontier.

Target:

    R_remote,weighted(center,source)
      <= kappa_s(beta,s) * W_center(source)

with a concrete coefficient independent of periodic spatial volume.

Required final strictness:

    rho_s + kappa_s(beta,s) < 1

for a nonempty parameter regime.

Preferred proof architecture:

    actual one-link law / fixed-target physical envelope
      -> weighted response inequality
      -> local Green propagation
      -> self-consistent remote forcing estimate
      -> weighted bootstrap / absorption
      -> explicit kappa_s.

A schematic form is

    response
      <= direct local term
        + G_local (remote forcing(response)).

The weight should be preserved throughout the argument.

Do **not** close this phase by:

    * postulating the desired kappa_s as a terminal assumption;
    * reverting to the coarse all-to-all tagged carrier as the spatial mechanism;
    * using the fixed-volume asymptotic constant from #4557 as though it decayed with distance;
    * using terminal covariance decay, a physical contraction,
      Poincare/coercivity, or a mass gap upstream.

The final theorem must derive the remote coefficient from already-authorized physical law/envelope machinery.

---

# Phase 12 — Strict weighted physical influence and spatial response decay

**Status: OPEN AFTER PHASE 11.**

Once Phase 11 supplies a concrete `kappa_s`, combine it with #4561:

    full weighted column
      <= (rho_s + kappa_s) W.

Under

    rho_s + kappa_s < 1,

derive strict weighted physical influence control and the corresponding weighted response/resolvent estimates.

The target is a genuine volume-independent spatial mechanism.

This phase should convert weighted operator control into explicit source-to-target decay without reintroducing the dense tagged carrier.

---

# Phase 13 — Terminal kernel-section base-L1 covariance decay

**Status: OPEN AFTER PHASE 12.**

Combine:

    source-singleton terminal variation
      + fixed-volume covariance-remainder closure from #4548
      + strict weighted physical influence control
      + exact kernel-section covariance mechanics.

Target schematic form:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^baseL1Distance(target,source),

uniformly in periodic volume, with

    C >= 0,
    0 <= q < 1.

This is the missing analytic input for the already-built downstream uniform-residual pipeline.

---

# Phase 14 — Uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Once Phase 13 is proved:

    terminal covariance decay
      -> terminal response decay
      -> cubic base-L1 shell summability
      -> volume-uniform remote residual
      -> strict physical sweep gate.

The source-aligned remote shell has a volume-independent polynomial growth bound, so a fixed exponential decay factor is summable.

Directionality is permanent:

    covariance decay -> uniform remote residual

is downstream and must not be used circularly to prove the same covariance decay.

---

# Phase 15 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After a volume-independent strict physical sweep contraction:

    physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

The target is a volume-independent coercive constant.

---

# Phase 16 — Uniform finite-volume transfer/Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

The required output is a positive spectral lower bound uniform over the finite periodic volumes used in the limiting construction.

A gap constant that collapses with volume is insufficient for the continuum target.

---

# Phase 17 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap, the program still requires:

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

Existing scalar or auxiliary continuum lanes are infrastructure, not substitutes for the full gauge-field construction.

---

# Phase 18 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The current repository should therefore be read as a rigorous formalization program with substantial finite-volume and analytic infrastructure, not as an already completed Clay solution.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4561:

    1. inspect the actual fixed-target / source-aligned physical envelope
       interfaces already proved at law level;

    2. formulate a weighted response inequality using
         W_center(x)=s^baseL1Distance(center,x)
       and the merged local resolvent from #4560;

    3. derive the actual weighted remote residual coefficient
         R_remote,weighted <= kappa_s W
       without assuming it;

    4. prove a nonempty parameter regime with
         18*eta(beta)*s^2 + kappa_s < 1;

    5. instantiate #4561 to obtain strict weighted subinvariance
       of the full physical-left influence envelope;

    6. derive the corresponding volume-independent weighted
       response / spatial decay theorem;

    7. combine that result with the already-closed #4548
       covariance remainder to obtain terminal base-L1
       covariance decay;

    8. invoke the cubic-shell pipeline to obtain a
       volume-uniform remote residual;

    9. close the strict physical sweep gate;

    10. derive physical Poincare/coercivity;

    11. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

    12. advance the thermodynamic/continuum physical Yang--Mills carrier;

    13. only then close the Clay-level existence and mass-gap statement.

---

# Current conceptual transition

    #4547
      exact complete-block / original-step iterate identity

    #4548
      fixed-volume covariance remainder
        Cov(F, P_scan^(n*L_H) G) -> 0

    #4551-#4553
      eligible pullback random-scan resolvent
      + exact coarse physical row coefficient
      + explicit fixed-volume obstruction

    #4554-#4557
      auxiliary unscanned response
      -> represented fixed-right source
      -> finite-step fixed-right response
      -> asymptotic fixed-right response

    #4558
      asymptotic fixed-right response transported back to
      actual source-aligned remote physical forcing

    #4559
      exponential weighted genuine local-Harnack Schur bound

    #4560
      K_local^d W <= rho_s^d W
      + G_local,M W <= (1-rho_s)^(-1) W

    #4561
      exact full weighted column
        = local weighted column + actual remote weighted column
      + abstract absorption gate

    current frontier
      derive the actual remote coefficient kappa_s
      non-circularly and volume-independently.

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
    fixed-right asymptotic bound != volume-uniform spatial decay
    exact weighted decomposition != proof of a remote coefficient
    abstract absorption interface != proof of strict absorption
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

These boundaries remain part of the formal proof architecture, not editorial caveats.
