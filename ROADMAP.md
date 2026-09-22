# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of itakura-hidetoshi/4d-mass-gap as of **2026-09-22 JST**.

Authoritative theorem-carrier branch:

    formal/real-hilbert-uniform-coercive-strong-limit

Exact theorem-bearing mathematical baseline for this refresh:

    30d54b17c3d1a9b7e243c4079e18e533d2e070c9

This is the merge commit of PR #4625:

    Prove fixed-contour Riesz projector idempotence

Documentation-only commits after this SHA do not change the theorem-bearing mathematical baseline.

Authority order:

    1. exact current GitHub theorem-carrier SHA
    2. formal Lean theorem artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

When histories differ, main is not theorem authority.

---

# Development map

    A. FINITE WILSON / OS / PHYSICAL TRANSFER ROOT             [INTEGRATED]
       -> finite periodic compact SU(N) model
       -> reflection positivity / OS carriers
       -> physical one-slab transfer
       -> finite-volume spectral architecture

    B. EXACT ONE-LINK / COVARIANCE MECHANICS                  [INTEGRATED]
       -> normalized continuous one-link law
       -> conditional expectation / L2 projection
       -> deterministic / random-scan telescopes
       -> fixed-volume covariance remainder closure

    C. GENUINE LOCAL EXPONENTIAL SPATIAL THEORY               [INTEGRATED]
       -> active-neighbor degree <= 18
       -> base-L1 exponential weights
       -> local Harnack kernel
       -> local weighted Green/resolvent bound

    D. CANONICAL FIXED-RIGHT RESPONSE                          [CLOSED]
       -> literal response value sets
       -> canonical supremum profile R_can
       -> minimality
       -> crude 0 <= R_can <= exp(16 beta)

    E. PIN-FREE RESPONSE-CONTROLLED DYNAMICS                   [CLOSED]
       -> remove distinguished-target pin
       -> pin-free physical kernel
       -> exact source-forcing recurrence
       -> fixed-volume terminal removal

    F. AGGREGATE REMOTE FAMILY / CANONICAL COLUMN              [CLOSED]
       -> weighted target aggregation
       -> exact finite superposition
       -> aggregate remote resolvent
       -> canonical remote column
       -> no target-cardinality loss

    G. LOCAL C5 EXCEPTIONAL COLUMN                             [CLOSED]
       -> fixed-right Harnack comparison
       -> canonical pointwise response bound
       -> finite C5 weighted-column estimate

    H. EXACT CANONICAL COEFFICIENT M_can                       [CLOSED]
       -> exact finite source maximum
       -> self-certificate
       -> bootstrap map Phi
       -> M_can(0)=0
       -> half-barrier exclusion M_can != 1/2

    I. CONTINUATION REDUCTION                                  [CLOSED]
       -> continuity of M_can implies M_can < 1/2
       -> M_can continuity reduced to response-coordinate continuity

    J. FINITE-VOLUME SPECTRAL BETA CONTINUATION                [CLOSED THROUGH #4613]
       -> top-ray uniqueness
       -> transfer Lipschitz in beta
       -> normalized transfer continuity
       -> complex fixed-z resolvent beta-continuity
       -> fixed canonical Riesz contour persistence

    K. FIXED-CONTOUR RIESZ CONTINUATION                        [CLOSED THROUGH #4625]
       -> fixed-contour projector beta-continuity
       -> base identification Q_beta0 = P_beta0
       -> complex canonical top sector rank one
       -> bilateral absorption of nearby P_beta
       -> radial resolvent margin / contour deformation
       -> separated-circle Fubini / Cauchy kernel calculus
       -> double-resolvent identity
       -> local idempotence Q_beta^2 = Q_beta

    L. RANK PERSISTENCE / NEARBY PROJECTOR IDENTIFICATION      [OPEN NOW]
       -> norm-closeness to rank-one P_beta0
       -> rank(Q_beta) <= 1
       -> absorption + nonzero P_beta => Q_beta != 0
       -> rank(Q_beta) = 1
       -> range(P_beta) = range(Q_beta)
       -> Q_beta = P_beta
       -> canonical moving projector beta-continuity

    M. CONTINUOUS CANONICAL POSITIVE TOP MODE                  [OPEN AFTER L]
       -> local continuous top line
       -> canonical normalization
       -> positivity-compatible continuous vacuum/top vector

    N. FIXED-RIGHT RESPONSE BETA CONTINUITY                    [OPEN AFTER M]
       -> continuous ground-state kernel section
       -> continuous normalized fixed-right law
       -> coordinatewise R_can continuity
       -> continuity of M_can

    O. HALF-BARRIER DISCHARGE / STRICT SPATIAL RESPONSE        [OPEN DOWNSTREAM]
       -> M_can < 1/2
       -> strict c_pf(beta,s,M_can) < 1
       -> weighted physical influence
       -> spatial response decay
       -> covariance decay
       -> coercivity / uniform finite-volume gap
       -> thermodynamic / continuum program

---

# Phase 1 — Finite Wilson / OS root

**Status: integrated.**

The repository contains the finite periodic compact SU(N) Wilson model, reflection-positive / OS carrier architecture, physical one-slab transfer construction, and the finite-volume spectral objects used downstream.

Boundary:

    finite-volume spectral structure
      != volume-uniform or continuum mass gap.

---

# Phase 2 — Exact one-link and covariance mechanics

**Status: closed.**

The normalized continuous one-link law, one-link conditional expectation, L2 projection identities, deterministic/random-scan telescopes, and fixed-volume covariance-remainder closure are integrated.

In particular, along complete random-scan blocks,

    Cov_mu(F, P_scan^(n * L_H) G) -> 0.

Boundary:

    fixed-volume remainder vanishing
      != volume-uniform spatial covariance decay.

---

# Phase 3 — Genuine local weighted Harnack theory

**Status: closed through #4560.**

With

    W_center(x) := s ^ baseL1Distance(center,x),

the sparse local physical kernel has weighted coefficient

    rho_s := 18 * eta(beta) * s^2.

The local iterated estimate and finite Green/resolvent bound are volume-independent in the spatial volume under rho_s < 1.

---

# Phase 4 — Canonical fixed-right response and pin-free dynamics

**Status: closed through #4595.**

PRs #4583-#4584 construct the actual canonical response profile R_can, prove its pointwise minimality among nonnegative uniform response profiles, and establish

    0 <= R_can(target,source) <= exp(16 * beta).

PRs #4586-#4595 remove the obsolete distinguished-target pin and carry the pin-free coefficient

    c_pf(beta,s,M)
      := 18 * eta(beta) * s^2
         + exp(16 * beta) * M

through finite-step dynamics, source forcing, stationary response, terminal control, and canonical remote closure.

---

# Phase 5 — Aggregate remote family and local C5 column

**Status: closed through #4603.**

PRs #4597-#4600 remove target-cardinality loss by aggregating the full remote target family before taking the canonical supremum.

PRs #4601-#4603 separately control the finite C5 exceptional column with explicit volume-independent coefficient

    20 * s^2 * exp(16 * beta) * eta_R(beta).

---

# Phase 6 — Exact canonical coefficient and half-barrier architecture

**Status: closed through #4608 except for the model-facing continuity input.**

PR #4605 defines the actual finite-volume canonical weighted coefficient M_can and proves its self-certificate / bootstrap properties together with

    M_can(beta=0) = 0.

PR #4606 proves, on a strictly positive volume-independent high-temperature interval,

    M_can != 1/2.

PR #4607 proves

    M_can continuous
      + M_can(0)=0
      + M_can never equals 1/2
      -> M_can < 1/2.

PR #4608 reduces continuity of M_can to coordinatewise beta-continuity of the canonical response profile.

---

# Phase 7 — Finite-volume top-ray and transfer beta continuation

**Status: closed through #4613.**

PR #4609 proves finite-volume uniqueness of the physical top ray.

PR #4610 proves operator-norm Lipschitz continuity in beta of the actual physical one-slab transfer and its top norm.

PR #4611 proves continuity of the normalized transfer on Set.Ici 0, with normalized top spectral point fixed at 1.

PR #4612 proves complex normalized transfer continuity and fixed-z resolvent continuity.

PR #4613 proves persistence of the entire canonical beta0 Riesz circle in the nearby resolvent set.

---

# Phase 8 — Fixed-contour Riesz projector beta continuity

**Status: closed through #4616.**

For the contour fixed at the canonical beta0 radius, define

    Q_beta
      := (2*pi*i)^(-1)
         * integral_{|z-1|=r_beta0} resolvent(S_beta,z) dz.

PR #4616 proves

    Q_beta -> Q_beta0

in operator norm as beta -> beta0.

At the base coupling,

    Q_beta0 = P_beta0,

where P_beta0 is the canonical CFC top spectral projection.

Permanent boundary:

    Q_beta continuous
      != moving canonical P_beta continuous

until nearby equality is proved.

---

# Phase 9 — Complex top-sector rank one

**Status: closed through #4617.**

PR #4617 proves that the real physical top eigenspace is the real span of the canonical nonnegative top vector and transports that uniqueness to the genuine complex physical carrier.

It identifies

    range(P_beta)

with a one-dimensional complex span.

This is a finite-volume rank-one theorem only.

---

# Phase 10 — Bilateral fixed-contour absorption

**Status: closed through #4618.**

For beta sufficiently near beta0, PR #4618 proves

    Q_beta * P_beta = P_beta,

    P_beta * Q_beta = P_beta.

Hence

    range(P_beta) subset range(Q_beta).

This does not yet imply equality of the projectors because the rank/range of Q_beta is not yet known.

---

# Phase 11 — Local radial contour-deformation infrastructure

**Status: closed through #4619.**

PR #4619 adds the local analytic machinery required for idempotence without assuming nearby gap continuity:

- two-point resolvent identity;
- compact radial spectrum;
- protected radial resolvent margin;
- resolvent differentiability/continuity on the protected annulus;
- contour-radius deformation inside that annulus.

---

# Phase 12 — Separated-circle Fubini and Cauchy calculus

**Status: closed through #4622.**

PR #4620 adds the pinned-compatible Fubini helper for nested circle integrals.

PR #4621 adds the exterior-pole zero integral and the signed interior-pole Cauchy-kernel identity.

PR #4622 proves integrability of the separated-circle resolvent kernel on the compact parameter rectangle.

These are support theorems for the actual idempotence argument; they do not themselves identify spectral projectors.

---

# Phase 13 — Separated-circle double-resolvent identity

**Status: closed through #4624.**

PR #4624 proves the general identity that collapses the separated outer/inner double resolvent integral to one factor of 2*pi*i times the inner resolvent integral.

The proof uses:

    resolvent identity
      -> inner exterior-pole cancellation
      -> Fubini
      -> outer interior-pole Cauchy evaluation.

PR #4623 was superseded and not merged; #4624 is the canonical merged version.

---

# Phase 14 — Fixed-contour Riesz idempotence

**Status: closed through #4625.**

PR #4625 proves

    for beta sufficiently near beta0,
      Q_beta^2 = Q_beta.

The proof deforms the fixed beta0 contour to separated inner/outer contours inside a protected local resolvent annulus, applies the double-resolvent identity, and returns to the original radius.

No continuity of the excited-sector gap is used.

No nearby equality Q_beta = P_beta is assumed.

This is the current theorem-bearing endpoint.

---

# Phase 15 — Rank-one persistence of the fixed-contour idempotent

**Status: OPEN — immediate theorem frontier.**

Use PR #4616 and PR #4625:

    Q_beta -> P_beta0 in operator norm,
    Q_beta^2 = Q_beta,
    rank(P_beta0) = 1.

A natural local route is:

    eventually ||Q_beta - P_beta0|| < 1
      -> P_beta0 restricted to range(Q_beta) is injective
      -> finrank(range(Q_beta)) <= 1.

Concretely, if

    x in range(Q_beta)
    and P_beta0 x = 0,

then idempotence gives Q_beta x = x, so

    x = (Q_beta - P_beta0) x.

The strict operator-norm bound then forces x=0.

This phase must be formalized explicitly; rank stability is not to be inferred informally from norm continuity alone.

---

# Phase 16 — Identify the nearby fixed-contour projector with the canonical top projector

**Status: OPEN AFTER PHASE 15.**

PR #4618 gives

    range(P_beta) subset range(Q_beta).

PR #4617 gives

    rank(P_beta) = 1.

Once Phase 15 proves rank(Q_beta) <= 1, absorption of the nonzero P_beta forces Q_beta to be nonzero, hence rank one.

Then

    range(P_beta) = range(Q_beta).

Using idempotence / absorption, close the operator equality

    Q_beta = P_beta.

This is the missing bridge from fixed-contour continuation to the moving canonical CFC spectral projector.

---

# Phase 17 — Canonical moving top-projector beta continuity

**Status: OPEN AFTER PHASE 16.**

Combine

    Q_beta = P_beta locally
      + beta-continuity of Q_beta from #4616

to obtain beta-continuity of the actual moving canonical CFC top projector.

This is stronger than the already-proved fixed-contour continuity and should not be claimed before Phase 16 closes.

---

# Phase 18 — Continuous canonical positive top mode

**Status: OPEN AFTER PHASE 17.**

Use

    beta-continuous canonical rank-one projector
      + top-ray uniqueness
      + existing positivity
      + fixed normalization

to construct a canonical normalized positive top vector continuously in beta.

One-dimensionality alone does not produce a continuous normalized vector without an explicit local selection and phase/sign normalization.

---

# Phase 19 — Fixed-right kernel-section and response beta-continuity

**Status: OPEN AFTER PHASE 18.**

Transport the continuous top mode into the ground-state kernel-section law used by the fixed-right response.

Then prove, for each fixed target/source coordinate,

    beta -> R_can(beta,target,source)

is continuous on the required high-temperature interval.

Apply #4608 to obtain continuity of the exact finite maximum M_can.

---

# Phase 20 — Discharge the canonical half-barrier continuation

**Status: OPEN AFTER PHASE 19.**

Combine

    M_can(0)=0,
    M_can continuous,
    M_can != 1/2

to conclude

    M_can < 1/2

throughout the selected nonempty high-temperature interval.

Then use monotonicity in M to obtain the strict canonical pin-free weighted coefficient.

---

# Phase 21 — Strict weighted physical influence and spatial response decay

**Status: OPEN DOWNSTREAM.**

Instantiate the pin-free physical kernel with the actual canonical response profile and prove

    K_can W <= c_s W,
    c_s < 1,

uniformly in periodic spatial volume in the selected high-temperature regime.

Then derive source-to-target response/resolvent decay.

---

# Phase 22 — Terminal base-L1 covariance decay

**Status: OPEN DOWNSTREAM.**

Combine strict weighted physical response, fixed-volume covariance-remainder closure, exact kernel-section covariance mechanics, and terminal variation to obtain a volume-uniform bound of the schematic form

    |Cov_mu(source,target)|
      <= C * q^baseL1Distance(target,source),

with 0 <= q < 1.

---

# Phase 23 — Uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Use cubic base-L1 shell summability:

    spatial response/covariance decay
      -> summable remote response
      -> volume-uniform remote residual
      -> strict physical sweep contraction.

Directionality is permanent; the remote residual is downstream of spatial decay.

---

# Phase 24 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After a volume-independent strict physical sweep estimate:

    physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

The coercive constant must remain uniform in volume.

---

# Phase 25 — Uniform finite-volume transfer / Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

Target a positive lower spectral bound uniform over the finite periodic volumes used in the limiting construction.

The finite-volume top isolation used in #4609-#4625 is a local spectral-continuation tool and must not be confused with this later volume-uniform gap.

---

# Phase 26 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After the required volume-uniform physical estimates, the program still requires

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

Existing auxiliary or scalar continuum lanes remain infrastructure, not substitutes for the full gauge-field construction.

---

# Phase 27 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The repository should therefore be read as a rigorous formalization program with substantial finite-volume, response-theoretic, and local spectral-continuation infrastructure, not as an already completed Clay solution.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline PR #4625:

    1. obtain an eventual strict norm bound
         ||Q_beta - P_beta0|| < 1;

    2. use idempotence of Q_beta to prove injectivity of
         P_beta0 restricted to range(Q_beta);

    3. deduce finrank(range(Q_beta)) <= 1;

    4. combine bilateral absorption with nonzero rank-one P_beta
         to prove Q_beta is nonzero and rank one;

    5. identify range(Q_beta) = range(P_beta);

    6. close Q_beta = P_beta;

    7. combine with #4616 to prove beta-continuity of the
         canonical moving CFC top projector;

    8. construct a continuous canonical positive normalized top mode;

    9. prove continuity of the fixed-right ground-state kernel-section law;

    10. prove coordinatewise beta-continuity of R_can;

    11. invoke #4608 to obtain continuity of M_can;

    12. invoke #4607 to prove M_can < 1/2 on the selected interval;

    13. instantiate the strict pin-free canonical weighted coefficient;

    14. derive volume-independent source-to-target spatial response decay;

    15. close the covariance-decay / uniform-remote-residual /
        coercivity / uniform-gap route before advancing the continuum claim.

---

# Current conceptual transition

    #4604-#4608
      exact canonical coefficient M_can
      -> half-barrier exclusion
      -> continuity reduction

    #4609-#4613
      top-ray uniqueness
      -> transfer beta-continuity
      -> complex resolvent beta-continuity
      -> fixed Riesz contour persistence

    #4616
      fixed contour
      -> operator-norm continuous Riesz continuation Q_beta

    #4617-#4618
      canonical top sector rank one
      -> Q_beta absorbs P_beta on both sides

    #4619-#4622
      radial resolvent margin
      -> contour deformation
      -> Fubini / Cauchy support
      -> separated-circle integrability

    #4624-#4625
      double-resolvent identity
      -> fixed-contour idempotence Q_beta^2 = Q_beta

    current frontier
      norm-close idempotent + base rank one
      -> rank-one persistence of Q_beta
      -> Q_beta = P_beta
      -> canonical moving projector beta-continuity
      -> beta-continuous positive vacuum
      -> beta-continuous fixed-right response
      -> discharge M_can half-barrier continuation.

---

# Permanent semantic boundaries

    finite-volume theorem != continuum theorem
    fixed-volume ergodicity != volume-uniform physical contraction
    random-scan mixing != spatial correlation decay
    covariance identity != covariance decay
    covariance decay != mass gap
    canonical response profile != continuity of that profile
    exact M_can != strict bound on M_can without continuation
    M_can != 1/2 != M_can < 1/2 without continuity
    top-ray uniqueness != continuous top-vector selection
    operator-norm transfer continuity != projector continuity
    pointwise resolvent continuity != contour-uniform continuity
    fixed-contour Q_beta continuity != moving P_beta continuity
    rank(P_beta0)=1 != rank(Q_beta)=1 without persistence
    Q_beta^2=Q_beta != Q_beta=P_beta
    bilateral absorption != equality without rank/range control
    fixed-volume top isolation != uniform thermodynamic gap
    uniform finite-volume gap != continuum Yang--Mills mass gap.

These boundaries are part of the theorem architecture, not editorial caveats.
