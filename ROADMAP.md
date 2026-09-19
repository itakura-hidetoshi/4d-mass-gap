# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-20 JST**.

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this refresh is:

    3a04b0c4fe02dcfffe4b02b9efc39be56c3deb48

This is the merge commit of PR #4542:

    Iterate Doeblin block observable contraction geometrically

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
       -> one-slab transfer and ground-state structure
       -> coercivity / spectral interfaces

    B. CONTINUOUS ONE-LINK REFERENCE LAW + LOCAL GEOMETRY       [INTEGRATED]
       -> normalized fiber probability law
       -> measurable heat-bath reinsertion
       -> stationarity / represented-source cancellation
       -> active-neighbor degree <= 18
       -> C5 exceptional set <= 20

    C. EXACT KERNEL-SECTION L2 / COVARIANCE STRUCTURE           [INTEGRATED]
       -> conditional expectation
       -> projection / fluctuation identities
       -> one-link covariance Dirichlet identity
       -> deterministic schedule telescope
       -> restricted-random-scan finite covariance resolvent

    D. SOURCE LOCALIZATION + DENSE-CARRIER OBSTRUCTION          [INTEGRATED]
       -> source crossing variation is singleton-supported
       -> coarse distinct-fiber profile is spatially flat off target

    E. ACTUAL LOCAL HARNACK / BASE-L1 GREEN ROUTE               [INTEGRATED]
       -> local step changes base-L1 distance by <= 2
       -> exact local Harnack kernel
       -> finite propagation of powers
       -> finite Green tail rho_local^D/(1-rho_local)
       -> local + remote perturbation
       -> singleton direct term inherits spatial decay

    F. WEIGHTED REMOTE CONVOLUTION                              [INTEGRATED #4526-#4527]
       -> coarse column-mass fallback
       -> base-L1 local Green weight
       -> W_remote(target,source)

    G. FIXED-RIGHT WEIGHTED BRIDGE                              [INTEGRATED #4529]
       -> source-aligned physical remote residual
          <= fixed-right finite-step target-response bound
       -> weighted remote column
          <= configuration-independent fixed-right weighted profile

    H. FIXED-RIGHT WEIGHTED SPATIAL CONTROL                     [OPEN NOW]
       -> prove base-L1 decay / weighted Schur / subinvariant estimate
       -> must not assume final terminal covariance decay

    I. ONE-LINK HAAR MINORIZATION                               [INTEGRATED #4530-#4531]
       -> reference one-link law dominates Haar
       -> heat-bath kernel inherits the lower bound

    J. DETERMINISTIC SCHEDULE HAAR ROUTE                        [INTEGRATED #4532-#4536]
       -> finite schedules are Markov kernels
       -> Haar-refresh kernel
       -> schedule minorization
       -> complete Haar sweep forgets initial state

    K. ACTUAL RESTRICTED RANDOM SCAN                            [INTEGRATED #4537]
       -> Markov kernel
       -> exact stationarity of the normalized reference law

    L. COMPLETE-BLOCK DOEBLIN MINORIZATION                      [INTEGRATED #4538-#4539]
       -> prescribed schedule occurs with exact selection product
       -> delta * nu_Haar <= P_block(A,·)
       -> delta > 0 at fixed finite volume
       -> P_block(A,·) = delta*nu_Haar + residual_A
       -> residual mass rho = 1-delta < 1

    M. FULL-BLOCK COUPLING                                      [INTEGRATED #4540]
       -> exact marginals
       -> common Haar mass coupled diagonally
       -> mismatch probability <= rho

    N. OBSERVABLE CONTRACTION                                   [INTEGRATED #4541-#4542]
       -> one block: oscillation <= rho * R
       -> n blocks: oscillation <= rho^n * R
       -> strong measurability preserved under iteration

    O. FIXED-VOLUME ERGODIC LIMIT                              [OPEN NOW]
       -> prove rho.toReal^n -> 0
       -> initial-state independence of the block-iterate limit
       -> identify the limit with the stationary reference expectation

    P. RANDOM-SCAN COVARIANCE REMAINDER CLOSURE                 [OPEN NEXT]
       -> evaluate the existing covariance remainder at complete-block times
       -> prove Cov(F, P_scan^(n*L_H) G) -> 0
       -> no volume-uniform Doeblin rate required

    Q. EXACT TERMINAL KERNEL-SECTION COVARIANCE DECAY           [OPEN]
       -> combine E + G + H + P
       -> prove volume-uniform base-L1 exponential decay

    R. UNIFORM REMOTE RESIDUAL / PHYSICAL SWEEP GATE            [OPEN DOWNSTREAM]
       -> cubic shell summability
       -> uniform remote residual
       -> strict physical sweep contraction

    S. PHYSICAL POINCARE / COERCIVITY                           [OPEN DOWNSTREAM]

    T. UNIFORM FINITE-VOLUME TRANSFER / HAMILTONIAN GAP         [OPEN DOWNSTREAM]

    U. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                 [OPEN DOWNSTREAM]

    V. CLAY-LEVEL EXISTENCE + MASS GAP                          [OPEN]

---

# Phase 0 — Authority and proof discipline

**Status: integrated and permanent.**

For theorem-bearing work:

    fresh-fetch theorem-carrier
    -> lock exact canonical SHA
    -> inspect exact Lean interfaces and the full changed file
    -> state one mathematically coherent theorem unit
    -> push and observe the PR current head
    -> query CI for that exact head
    -> repair genuine Lean/API/syntax errors without weakening
    -> require completed/success on the exact current head
    -> require the exact-head CI receipt
    -> merge against the expected head SHA
    -> fresh-fetch canonical again.

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

# Phase 2 — Continuous one-link law and physical local geometry

**Status: integrated.**

The repository contains the normalized continuous one-link law, measurable heat-bath reinsertion, one-link stationarity/properness machinery, and the physical C5/local-neighbor geometry.

Key local facts:

    active spatial plaquette-neighbor degree <= 18
    C5 exceptional set cardinality <= 20.

The old dense distinct-fiber carrier remains a valid coarse upper bound but is not the actual sparse spatial carrier.

---

# Phase 3 — Exact kernel-section covariance mechanics

**Status: integrated through #4513.**

The exact kernel-section one-link update is identified with conditional expectation on the relevant off-fiber sigma-algebra. The repository contains the associated `L2` projection/fluctuation identities, covariance self-adjointness, one-link Dirichlet identity, deterministic schedule telescope, and restricted-random-scan finite covariance resolvent.

The finite covariance telescope has schematic form

    |Cov(F,G) - Cov(F,P_scan^M G)|
      <= finite resolvent pairing.

Permanent boundary:

    finite resolvent
      != vanishing covariance remainder.

---

# Phase 4 — Source-singleton localization and dense-carrier obstruction

**Status: integrated through #4515-#4516.**

The source crossing variation is singleton-supported, so the finite-resolvent pairing collapses to a single source coordinate.

The coarse distinct-fiber carrier is proved spatially flat off target. Therefore repeated sharpening of that distance-blind carrier cannot be the final mechanism for base-`L1` covariance decay.

---

# Phase 5 — Actual local Harnack finite propagation and Green tail

**Status: integrated through #4518-#4525.**

One actual plaquette-local step changes periodic link-base `L1` distance by at most two.

The actual local Harnack kernel `K_local` has row/column mass bounded by

    rho_local(beta) := 18 * eta_local(beta),

and its powers satisfy exact finite propagation:

    K_local^d(target,source) != 0
      -> baseL1Distance(target,source) <= 2*d.

Under `rho_local < 1`, the finite local resolvent has the geometric bound

    R_local,M(target,source)
      <= rho_local^D/(1-rho_local)

whenever the target/source distance is at least `2D`.

The full comparison is reorganized as

    w
      <= G_local,M v
        + G_local,M(R_remote w)
        + K_local^M w,

so only the genuine local kernel is iterated. Remote smallness is not assumed.

Singleton forcing inherits the same local Green decay.

---

# Phase 6 — Weighted remote convolution

**Status: integrated through #4526-#4527.**

The coarse fallback reduces remote forcing to source-column mass but loses spatial information.

The preferred route defines

    G_weight(target,mid)
      := rho_local^floor(baseL1Distance(target,mid)/2)
         / (1-rho_local),

and

    W_remote(target,source)
      :=
    sum_mid
      G_weight(target,mid)
      * R_remote(source,mid).

Then

    G_local,M(R_remote w)(target)
      <=
    sum_source W_remote(target,source) * w(source).

This preserves target/intermediate/source geometry.

---

# Phase 7 — Fixed-right finite-step bridge

**Status: integrated through #4529.**

PR #4529 proves:

    source-aligned physical remote residual
      <= fixed-right finite-step target-response bound.

The comparison is then lifted through the local Green weight, yielding a configuration-independent fixed-right finite-step weighted response profile dominating the actual weighted remote column.

This closes the old open task of merely connecting the source-aligned weighted perturbation route to fixed-right response machinery.

What remains open is quantitative **spatial control** of that fixed-right weighted profile.

---

# Phase 8 — One-link Haar minorization

**Status: integrated through #4530-#4531.**

Every reference one-link law admits a strictly positive Haar minorization. The actual heat-bath reinsertion kernel inherits the same lower-bound structure.

This is an independent fixed-volume ergodic route. It does not use terminal covariance decay, uniform remote smallness, a physical sweep contraction, Poincare/coercivity, or mass-gap input.

---

# Phase 9 — Finite deterministic schedules and complete Haar refresh

**Status: integrated through #4532-#4534 and #4536.**

Finite reference heat-bath schedules are packaged as kernels, and Haar minorization propagates through them.

A complete Haar-refresh sweep forgets the initial configuration exactly. The actual deterministic complete sweep dominates the same initial-state-independent Haar-refresh law.

PR #4535 was closed without merge and is not canonical.

---

# Phase 10 — Actual restricted random scan as a stationary Markov kernel

**Status: integrated through #4537.**

The actual restricted random scan is a Markov kernel. The normalized continuous-vacuum reference probability law is stationary.

This supplies the exact probabilistic object needed for an independent fixed-volume covariance-remainder closure.

---

# Phase 11 — Complete-block Doeblin minorization

**Status: integrated through #4538-#4539.**

Let `L_H` denote the complete schedule length.

A prescribed ordered schedule appears inside `L_H` actual random-scan steps with the exact product of uniform one-step selection coefficients.

Combining that event with the deterministic complete-sweep Haar minorization gives

    delta_{H,beta} * nu_Haar
      <= P_block(A, ·)

for every initial state `A`, with

    delta_{H,beta} > 0

at each fixed finite volume.

The coefficient is not claimed to be volume-uniform.

Each full block row decomposes exactly as

    P_block(A,·)
      = delta * nu_Haar + residual_A,

with

    residual_A(univ) = rho := 1-delta

and

    rho < 1.

---

# Phase 12 — Exact full-block coupling

**Status: integrated through #4540.**

The coupling uses the common Haar component diagonally and couples the residual pieces by a normalized product when the residual mass is nonzero.

The marginals are exactly the two full-block rows, and

    Pr[X != Y] <= rho.

This is the exact coupling input for bounded-test contraction.

---

# Phase 13 — One-block observable contraction

**Status: integrated through #4541.**

For every strongly measurable real observable `f` with global pairwise oscillation bound

    |f(X)-f(Y)| <= R,

the complete random-scan block satisfies

    |P_block f(A) - P_block f(C)|
      <= rho.toReal * R.

The coefficient is `rho`, not `2*rho`, because the common Haar component is coupled diagonally and contributes exactly zero to the observable difference.

---

# Phase 14 — Geometric block contraction

**Status: integrated through #4542.**

Full-block expectation iteration is formalized and preserves strong measurability.

For every `n`:

    |P_block^n f(A) - P_block^n f(C)|
      <= rho.toReal^n * R.

This is the current theorem-bearing endpoint of the fixed-volume Doeblin route.

---

# Phase 15 — Fixed-volume ergodic convergence

**Status: OPEN NOW.**

Immediate target:

    rho < 1
      -> rho.toReal < 1
      -> rho.toReal^n -> 0.

Use #4542 to deduce that `P_block^n f(A)` becomes independent of the initial configuration.

Then use exact stationarity of the normalized continuous-vacuum reference law to identify the common limit with

    E_mu[f].

A useful quantitative output is

    |P_block^n f(A) - E_mu[f]|
      <= rho.toReal^n * Osc(f),

or an equivalent theorem strong enough for the covariance remainder.

This phase is fixed-volume. A coefficient that decays with volume is acceptable.

---

# Phase 16 — Restricted-random-scan covariance remainder

**Status: OPEN NEXT.**

The existing covariance telescope contains

    Cov_mu(F, P_scan^M G).

The new block theory naturally controls complete-block times.

Preferred route:

    M_n := n * L_H

and prove an explicit identification between

    P_scan^(M_n) G

and

    P_block^n G.

Then combine Phase 15 with integrability/boundedness of the relevant observables to conclude

    Cov_mu(F, P_scan^(n*L_H) G) -> 0.

That is sufficient to close the finite-resolvent covariance telescope along a subsequence if the preceding identity is exact.

Do not confuse this remainder with the unrelated local-power remainder `rho_local^M * distanceBound`.

---

# Phase 17 — Fixed-right weighted spatial control

**Status: OPEN IN PARALLEL WITH PHASES 15-16.**

The configuration-independent fixed-right weighted response profile supplied by #4529 still needs an independent spatial estimate.

Target options:

    W_fixed(target,source)
      <= C_remote * q_remote^baseL1Distance(target,source),

with `0 <= q_remote < 1`, or a weighted Schur/subinvariant theorem strong enough to absorb the remote convolution in an exponential spatial norm.

Critical non-circularity constraint:

    final terminal covariance decay

must not be assumed as the premise that proves this weighted spatial estimate.

---

# Phase 18 — Exact terminal kernel-section covariance decay

**Status: OPEN AFTER PHASES 16 AND 17.**

Combine:

    source-singleton terminal variation
      + actual local Green decay
      + fixed-right weighted remote spatial control
      + restricted-random-scan covariance-remainder vanishing.

Target schematic form:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^baseL1Distance(target,source),

uniformly in periodic volume, with

    C >= 0,
    0 <= q < 1.

This is the missing analytic input for the already-built downstream uniform-residual pipeline.

---

# Phase 19 — Uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Once Phase 18 is proved, existing theorems give:

    terminal covariance decay
      -> terminal response decay
      -> cubic base-L1 shell summability
      -> volume-uniform remote residual
      -> strict physical sweep gate.

The source-aligned remote shell obeys a volume-independent cubic polynomial bound, so exponential decay with any fixed `0 <= q < 1` is summable.

Directionality is permanent:

    covariance decay -> uniform remote residual

is downstream and must not be used circularly to prove the same covariance decay.

---

# Phase 20 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After a volume-independent strict physical sweep contraction:

    physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

The target is a volume-independent coercive constant.

---

# Phase 21 — Uniform finite-volume transfer/Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

The required output is a positive spectral lower bound uniform over the finite periodic volumes used in the limiting construction.

A gap constant that collapses with volume is insufficient for the continuum target.

---

# Phase 22 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap, the program still requires:

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

Existing scalar or auxiliary continuum lanes are infrastructure, not substitutes for the full gauge-field construction.

---

# Phase 23 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The current repository should therefore be read as a rigorous formalization program with substantial finite-volume and analytic infrastructure, not as an already completed Clay solution.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4542:

    1. prove the real contraction-factor facts needed for limits:
         0 <= rho.toReal < 1;

    2. prove
         Tendsto (fun n => rho.toReal^n) atTop (nhds 0);

    3. use #4542 to prove initial-state independence of
         P_block^n f;

    4. use exact stationarity to identify the common limit with
         integral f dmu;

    5. connect block iteration to the original restricted-random-scan
       iterate at times M = n * L_H;

    6. close
         Cov_mu(F, P_scan^(n*L_H) G) -> 0;

    7. in parallel, prove a non-circular base-L1 decay or weighted
       operator estimate for the #4529 fixed-right weighted profile;

    8. combine the spatial route and covariance-remainder closure to
       prove exact terminal kernel-section base-L1 covariance decay;

    9. invoke the existing cubic-shell pipeline to obtain a
       volume-uniform remote residual;

    10. close the strict physical sweep gate;

    11. derive physical Poincare/coercivity;

    12. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

    13. advance the thermodynamic/continuum physical Yang--Mills carrier;

    14. only then close the Clay-level existence and mass-gap statement.

---

# Current conceptual transition

    #4513
      finite restricted-random-scan covariance resolvent

    #4515-#4516
      source singleton localization
      + proof that the old dense carrier loses spatial radius

    #4518-#4525
      actual local Harnack finite propagation
      + actual local Green tail
      + local/remote perturbation

    #4526-#4527
      remote forcing upgraded from global L1
      to base-L1 weighted convolution

    #4529
      weighted physical remote term bridged to
      configuration-independent fixed-right finite-step response

    #4530-#4536
      independent Haar-minorization route
      through complete deterministic sweeps

    #4537-#4540
      actual restricted random scan
      -> complete-block Doeblin lower bound
      -> residual mass rho < 1
      -> exact two-row coupling

    #4541-#4542
      one-block observable contraction
      -> geometric rho^n contraction

    current frontier
      (A) convert geometric block contraction into stationary convergence
          and covariance-remainder vanishing;
      (B) prove non-circular spatial control of the fixed-right weighted
          remote profile;
      (C) combine A+B with the local Green route to obtain terminal
          base-L1 covariance decay.

---

# Permanent semantic boundaries

    finite-volume theorem != continuum theorem
    fixed-volume ergodicity != volume-uniform physical contraction
    random-scan mixing != spatial correlation decay
    covariance identity != covariance decay
    covariance decay != mass gap
    one-link conditional expectation != full Gibbs-law identification
    source-aligned envelope != fixed-target kernel-section envelope
    local Harnack propagation != remote residual control
    weighted fixed-right bridge != weighted spatial decay
    finite local Green remainder != covariance remainder
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

These boundaries remain part of the formal proof architecture, not editorial caveats.
