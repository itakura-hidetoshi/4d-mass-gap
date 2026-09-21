# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of itakura-hidetoshi/4d-mass-gap as of **2026-09-21 JST**.

Authoritative theorem-carrier branch:

    formal/real-hilbert-uniform-coercive-strong-limit

Exact theorem-bearing baseline for this refresh:

    295700014db3661c046c3d56f57e6cca809c63c2

This is the merge commit of PR #4613:

    Prove canonical Riesz contour beta stability

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
       -> top / excited-sector spectral architecture

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
       -> exact literal response value sets
       -> canonical supremum profile R_can
       -> minimality among uniform response profiles
       -> crude 0 <= R_can <= exp(16 beta)

    E. PIN-FREE RESPONSE-CONTROLLED DYNAMICS                   [CLOSED]
       -> remove distinguished-target pin
       -> pin-free physical kernel
       -> law-level variation propagation
       -> random-scan orbit
       -> exact source-forcing recurrence
       -> stationary finite-step decomposition
       -> fixed-volume terminal removal

    F. AGGREGATE REMOTE FAMILY / CANONICAL COLUMN              [CLOSED]
       -> weighted target aggregation
       -> exact finite superposition of discrepancies
       -> aggregate remote resolvent
       -> canonical weighted remote column
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
       -> continuity of M_can reduced to coordinate response continuity

    J. FINITE-VOLUME SPECTRAL BETA CONTINUATION                [CLOSED THROUGH #4613]
       -> top-ray uniqueness
       -> transfer Lipschitz in beta
       -> normalized transfer continuity
       -> complex fixed-z resolvent beta-continuity
       -> fixed canonical Riesz contour persistence
       -> spectral-parameter continuity on nearby fixed contour

    K. RIESZ PROJECTOR / VACUUM BETA CONTINUITY                [OPEN NOW]
       -> beta-continuity of contour integral
       -> beta-continuous CFC top projector
       -> continuous positive normalized top vector
       -> continuous canonical vacuum / ground-state data

    L. CANONICAL RESPONSE BETA CONTINUITY                      [OPEN NEXT]
       -> fixed-right kernel-section law continuity
       -> coordinatewise R_can continuity
       -> M_can continuity
       -> discharge #4607 continuation theorem

    M. STRICT PIN-FREE WEIGHTED PHYSICAL INFLUENCE             [OPEN]
       -> M_can < 1/2 in nonempty high-temperature regime
       -> c_pf(beta,s,M_can) < 1
       -> strict weighted physical response propagation

    N. SPATIAL COVARIANCE DECAY / UNIFORM REMOTE RESIDUAL      [OPEN]
       -> source-to-target response decay
       -> terminal kernel-section base-L1 covariance decay
       -> cubic shell summability
       -> volume-uniform remote residual
       -> strict physical sweep contraction

    O. PHYSICAL POINCARE / COERCIVITY                           [OPEN]

    P. UNIFORM FINITE-VOLUME TRANSFER / HAMILTONIAN GAP        [OPEN]

    Q. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                [OPEN]

    R. CLAY-LEVEL EXISTENCE + MASS GAP                          [OPEN]

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

Queued or in-progress CI is not GREEN.

No new sorry, admit, axioms, hidden constants, hypothesis weakening, theorem weakening, or semantic broadening may replace proof.

---

# Phase 1 — Finite Wilson / OS root

**Status: integrated.**

The repository contains the finite periodic compact-SU(N) Wilson model, reflection-positive structures, one-slab transfer architecture, physical Hilbert carriers, nonnegative ground-state framework, and downstream spectral/coercivity interfaces.

Boundary:

    finite Wilson / OS infrastructure
      != completed continuum Yang--Mills existence theorem.

---

# Phase 2 — Continuous one-link law and exact covariance mechanics

**Status: integrated.**

The continuous one-link law is normalized and measurable. The repository contains heat-bath reinsertion, stationarity/properness machinery, one-link conditional expectation, L2 projection/fluctuation identities, covariance self-adjointness, deterministic-schedule telescopes, and restricted-random-scan covariance resolvents.

PRs #4547-#4548 close the fixed-volume covariance remainder along complete blocks:

    Cov_mu(F, P_scan^(n * L_H) G) -> 0.

Boundary:

    fixed-volume remainder vanishing
      != volume-uniform spatial covariance decay.

---

# Phase 3 — Genuine local weighted Harnack theory

**Status: closed through #4560.**

For

    W_center(x) := s ^ baseL1Distance(center,x),

with s >= 1, the sparse local physical kernel obeys

    K_local W <= rho_s W,

where

    rho_s := 18 * eta(beta) * s^2.

The iterated local estimate and finite Green/resolvent bound are formalized under rho_s < 1.

This is the volume-independent local geometric input used later in the response-controlled theory.

---

# Phase 4 — Fixed-target decomposition and response-controlled kernel

**Status: integrated through #4573, superseded in part by the later pin-free refinement.**

The actual fixed-target envelope was decomposed into local, target-pin, and remote pieces.

Weighted superposition and remote-response linearization then connected the actual remote residual to a fixed-right response profile.

PR #4573 introduced the response-controlled physical kernel K_R.

This stage established the architecture, but the later #4586-#4588 work removed the distinguished-target pin from the actual physical-left kernel. The pin-free formulation is now the preferred route.

---

# Phase 5 — Exact response-controlled finite-step dynamics

**Status: closed through #4582.**

PR #4577 normalizes the accumulated source discrepancy and proves the exact forcing-sum identity.

PR #4578 rebuilds the stationary fixed-right response decomposition using the response-controlled physical recurrence rather than the old dense tagged left-left carrier.

PRs #4579-#4580 derive weighted random-scan and source-forcing resolvent bounds.

PR #4581 proves the finite-volume terminal response tends to zero under the strict response-controlled weighted coefficient.

PR #4582 removes that terminal term and obtains a direct asymptotic fixed-right response bound.

This closes the finite-step-to-asymptotic response route without using terminal covariance decay or coercivity.

---

# Phase 6 — Canonical fixed-right response profile

**Status: closed through #4584.**

PR #4583 constructs the literal fixed-right response value sets and the canonical pointwise supremum profile R_can.

It proves:

    0 <= R_can(target,source) <= exp(16 * beta),

and that R_can dominates every literal fixed-right response.

PR #4584 proves R_can is pointwise minimal among nonnegative uniform response profiles and transports any weighted-column certificate to this canonical object.

The former circularity of solving for an arbitrary assumed profile has therefore been removed.

---

# Phase 7 — Remove the distinguished-target pin

**Status: closed through #4595.**

PR #4585 isolates the distinguished-target pin as the remaining obstruction in the older response-controlled weighted row.

PR #4586 proves a direct remote cross-ratio comparison for the distinguished-target fiber.

PR #4587 uses that result to define the pin-free response-controlled physical-left kernel:

    diagonal:
      0

    intrinsic active-neighbor term:
      eta(beta)

    otherwise:
      exp(16 * beta) * R(target,source).

Its weighted coefficient is

    c_pf(beta,s,M)
      := 18 * eta(beta) * s^2
         + exp(16 * beta) * M.

PRs #4588-#4594 carry this coefficient through weighted random scan, literal law variation, source forcing, stationary response, terminal control, and asymptotic terminal removal.

PR #4595 transports the resulting remote estimate to the canonical response profile.

The obsolete standalone distinguished-target +eta(beta) term is no longer part of the preferred physical-left recurrence.

---

# Phase 8 — Aggregate the complete remote target family

**Status: closed through #4600.**

PR #4597 defines the exponentially weighted aggregate of all singleton target-ratio variation profiles and proves the exact identity

    sum_target W_center(target) * V_target(e)
      = exp(16 * beta) * W_center(e).

PR #4598 proves exact scalar and finite-superposition linearity of the pin-free orbit, source forcing, and accumulated discrepancy.

PR #4599 applies the aggregate resolvent to arbitrary target-indexed response witnesses and removes the fixed-volume terminal term before taking the spatial conclusion.

PR #4600 lifts the result to the canonical supremum profile without assuming one common maximizing witness.

This is the key step that removes target-cardinality loss from the full remote weighted column.

---

# Phase 9 — Control the local C5 exceptional column

**Status: closed through #4603.**

PR #4601 proves a volume-independent Harnack comparison for the fixed-right ground-state kernel-section law.

PR #4602 transports that comparison to every literal fixed-right response and then to the canonical profile.

PR #4603 uses the finite C5 exceptional-set cardinality and weighted base-L1 geometry to obtain the explicit volume-independent exceptional-column coefficient

    20 * s^2 * exp(16 * beta) * eta_R(beta).

This coefficient vanishes at beta = 0.

---

# Phase 10 — Exact canonical weighted coefficient and bootstrap map

**Status: closed through #4605.**

PR #4604 combines the exceptional and remote pieces into the explicit improvement map

    Phi(beta,s,M).

Its pin-free denominator is controlled by

    c_pf(beta,s,M)
      = 18 * eta(beta) * s^2
        + exp(16 * beta) * M.

PR #4605 defines M_can as the actual finite maximum over source-normalized weighted canonical response columns.

It proves:

    M_can >= 0,

    M_can is a valid certificate for its own canonical response profile,

    c_pf(beta,s,M_can) < 1
      -> M_can <= Phi(beta,s,M_can),

and exactly

    M_can(beta = 0) = 0.

At this point the closure variable is the actual model coefficient, not an auxiliary unknown.

---

# Phase 11 — High-temperature half-barrier architecture

**Status: closed through #4608 except for the model-facing continuity input.**

PR #4606 fixes the barrier 1/2 and proves that for a strictly positive, volume-independent beta cutoff:

    c_pf(beta,s,1/2) < 1,

    Phi(beta,s,1/2) < 1/2,

and hence the actual canonical coefficient cannot equal the barrier:

    M_can != 1/2.

PR #4607 proves the continuation theorem:

    continuity of beta -> M_can
      + M_can(0)=0
      + exclusion of M_can=1/2
      -> M_can < 1/2

throughout the selected high-temperature interval.

PR #4608 reduces continuity of M_can to coordinatewise beta-continuity of the canonical fixed-right response profile.

Therefore the remaining problem in this phase is not scalar algebra. It is the beta-continuity of the underlying canonical physical response coordinates.

---

# Phase 12 — Top-ray uniqueness

**Status: closed through #4609.**

PR #4609 proves finite-volume uniqueness of the physical top ray.

For every fixed finite volume and nonnegative beta, every physical top eigenvector is a real scalar multiple of the canonical nonnegative top vector.

This removes the ambiguity that would otherwise obstruct a canonical continuous choice of top mode.

Boundary:

    top-ray uniqueness at each beta
      != continuity of the selected top vector in beta.

---

# Phase 13 — Physical transfer continuity in beta

**Status: closed through #4611.**

PR #4610 proves operator-norm Lipschitz continuity in beta of the genuine finite-volume physical one-slab transfer.

The same estimate controls its top-transfer norm.

PR #4611 packages beta >= 0 as the fixed half-line Set.Ici 0, proves continuity of the positive top norm and its reciprocal, and obtains operator-norm continuity of the normalized physical transfer.

The normalized top spectral point is fixed at

    1.

The constants here are allowed to depend on finite volume; this stage is local spectral continuation, not the later uniform mass-gap estimate.

---

# Phase 14 — Complex normalized resolvent continuity

**Status: closed through #4612.**

PR #4612 proves that canonical real-to-complex physical scalar extension is globally Lipschitz in operator norm.

It follows that

    beta -> S_beta

for the normalized complex physical one-slab transfer is operator-norm continuous.

For every fixed z belonging to the base resolvent set, the theorem then proves

    beta -> resolvent(S_beta,z)

is continuous at the base beta.

The proof uses continuity of inversion at a unit, not a spectral-gap continuity assumption.

This is pointwise-in-z continuity only.

---

# Phase 15 — Canonical Riesz contour beta stability

**Status: closed through #4613.**

At beta0, let the canonical Riesz radius be the existing positive half-gap radius around the isolated normalized top point 1.

PR #4613 proves:

    for all sufficiently nearby beta,
      Metric.sphere(1,r_beta0)
        subset resolventSet(S_beta).

The contour is fixed at the beta0 radius while the operator moves.

The proof uses:

    normalized transfer continuity
      -> joint shift continuity
      -> openness of the unit locus
      -> base-circle spectral isolation
      -> compactness of the circle
      -> generalized tube lemma.

On the same fixed contour, PR #4613 also proves that for every sufficiently nearby beta,

    z -> resolvent(S_beta,z)

is ContinuousOn the contour.

This is the compact spectral-persistence bridge needed before moving the Riesz projector itself.

---

# Phase 16 — Beta-continuity of the Riesz / CFC top projector

**Status: OPEN — immediate theorem frontier.**

The repository already proves at each fixed beta that the normalized contour integral equals the existing CFC top spectral projection:

    (2*pi*i)^(-1)
      * integral_circle resolvent(S_beta,z)
      = P_top(beta).

The next task is to make this identity vary continuously in beta.

The intended route is:

    fixed beta0 contour persists for nearby beta
      -> obtain joint or uniform-enough resolvent control on that contour
      -> pass beta-continuity through the circle integral
      -> obtain ContinuousAt beta0 of the Riesz projector
      -> identify it with P_top(beta).

Care is required because:

    pointwise beta-continuity for each z
      != automatically uniform contour continuity.

The proof should use compactness of the fixed circle rather than assume continuity of the excited-sector gap.

---

# Phase 17 — Continuous canonical positive top mode

**Status: OPEN AFTER PHASE 16.**

Use:

    beta-continuous top projector
      + top-ray uniqueness
      + existing positivity of the canonical top representative
      + fixed normalization

to construct a canonical positive normalized top vector continuously in beta.

The selection must remain compatible with the existing physical and CFC carriers.

Do not infer vector continuity merely from one-dimensionality without an explicit local selection/normalization theorem.

---

# Phase 18 — Fixed-right kernel-section and response beta-continuity

**Status: OPEN AFTER PHASE 17.**

Transport the continuous top mode into the ground-state kernel-section law used by the fixed-right response.

Then prove, for each fixed target/source coordinate,

    beta -> R_can(beta,target,source)

is continuous on the required high-temperature interval.

After coordinatewise continuity is established, apply #4608 to obtain continuity of the exact finite maximum M_can.

This closes the only remaining premise of the #4607 continuation theorem.

---

# Phase 19 — Discharge the canonical half-barrier continuation

**Status: OPEN AFTER PHASE 18.**

Combine:

    M_can(0)=0
      + M_can continuous
      + M_can != 1/2 on the selected interval

to conclude

    M_can < 1/2.

Because the cutoff also has

    c_pf(beta,s,1/2) < 1,

the monotonic dependence on M then yields the strict canonical pin-free weighted coefficient required for the physical response recurrence.

This is the point where the current high-temperature response closure becomes unconditional within the proved interval.

---

# Phase 20 — Strict weighted physical influence and spatial response decay

**Status: OPEN DOWNSTREAM.**

Instantiate the pin-free physical kernel with the actual canonical response profile and exact strict coefficient.

Target:

    K_can W <= c_s W,

with

    c_s < 1

uniformly in periodic spatial volume in the selected high-temperature regime.

Then derive volume-independent source-to-target response/resolvent decay.

The sparse physical kernel, not the old dense tagged carrier, must remain the propagation mechanism.

---

# Phase 21 — Terminal kernel-section base-L1 covariance decay

**Status: OPEN DOWNSTREAM.**

Combine:

    strict weighted physical response
      + fixed-volume covariance-remainder closure
      + exact kernel-section covariance mechanics
      + source-singleton terminal variation

to obtain a bound of the form

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^baseL1Distance(target,source),

uniformly in periodic volume, with

    C >= 0,
    0 <= q < 1.

This is the first genuine spatial covariance-decay theorem in the downstream route.

---

# Phase 22 — Uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Use cubic base-L1 shell summability:

    spatial covariance decay
      -> summable remote response
      -> volume-uniform remote residual
      -> strict physical sweep contraction.

Directionality is permanent:

    covariance/response decay
      -> uniform remote residual,

not the reverse.

---

# Phase 23 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After a volume-independent strict physical sweep estimate:

    physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

The required coercive constant must remain uniform in volume.

---

# Phase 24 — Uniform finite-volume transfer / Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

Target a positive spectral lower bound uniform over the finite periodic volumes used in the limiting construction.

A fixed-volume gap that collapses with volume is insufficient.

The finite-volume top isolation used in #4609-#4613 is a local spectral-continuation tool and must not be confused with this later volume-uniform gap.

---

# Phase 25 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After the required volume-uniform physical estimates, the program still requires:

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

Existing auxiliary or scalar continuum lanes remain infrastructure, not substitutes for the full gauge-field construction.

---

# Phase 26 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The repository should therefore be read as a rigorous formalization program with substantial finite-volume, response-theoretic, and spectral-continuation infrastructure, not as an already completed Clay solution.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline PR #4613:

    1. work on the fixed beta0 canonical Riesz circle;

    2. strengthen the available pointwise beta-resolvent continuity to the
       joint/uniform contour control needed by the circle integral;

    3. prove beta-continuity of the normalized Riesz projector;

    4. transport the result to the existing CFC top spectral projection;

    5. combine projector continuity with top-ray uniqueness and positivity
       to construct a continuous normalized positive top vector;

    6. prove continuity of the fixed-right ground-state kernel-section law;

    7. prove coordinatewise beta-continuity of the canonical response profile;

    8. invoke #4608 to obtain continuity of M_can;

    9. invoke #4607 to prove M_can < 1/2 on the selected nonempty
       high-temperature interval;

    10. instantiate the strict pin-free canonical weighted coefficient;

    11. derive volume-independent source-to-target spatial response decay;

    12. combine with the fixed-volume covariance remainder route to obtain
        terminal base-L1 covariance decay;

    13. run the cubic-shell / uniform-remote-residual pipeline;

    14. close physical sweep contraction, Poincare/coercivity,
        and the uniform finite-volume spectral gap;

    15. only then advance the thermodynamic/continuum Yang--Mills carrier
        and the Clay-level statement.

---

# Current conceptual transition

    #4577-#4582
      exact source-forcing recurrence
      -> stationary response
      -> terminal removal

    #4583-#4584
      arbitrary response profile
      -> actual canonical response profile R_can

    #4586-#4595
      remove distinguished-target pin
      -> pin-free response-controlled recurrence
      -> canonical remote resolvent

    #4597-#4600
      aggregate complete remote target family
      -> no target-cardinality loss
      -> canonical weighted remote column

    #4601-#4603
      fixed-right Harnack comparison
      -> finite C5 exceptional weighted column

    #4604-#4605
      combine local + remote columns
      -> exact canonical coefficient M_can
      -> self-bootstrap inequality

    #4606-#4608
      high-temperature half-barrier exclusion
      -> continuation theorem
      -> reduce M_can continuity to response-coordinate continuity

    #4609-#4613
      top-ray uniqueness
      -> transfer beta-continuity
      -> complex resolvent beta-continuity
      -> fixed Riesz contour persistence

    current frontier
      fixed-contour resolvent control
      -> beta-continuous Riesz/CFC top projector
      -> beta-continuous canonical positive vacuum
      -> beta-continuous fixed-right response
      -> discharge M_can half-barrier continuation.

---

# Permanent semantic boundaries

    finite-volume theorem != continuum theorem
    fixed-volume ergodicity != volume-uniform physical contraction
    random-scan mixing != spatial correlation decay
    covariance identity != covariance decay
    covariance decay != mass gap
    one-link conditional expectation != full Gibbs-law identification
    coarse tagged carrier != actual sparse physical carrier
    local weighted resolvent != canonical remote weighted closure
    canonical response profile != continuity of that profile
    exact M_can != strict bound on M_can without continuation
    M_can != 1/2 != M_can < 1/2 without continuity
    top-ray uniqueness != continuous top-vector selection
    operator-norm transfer continuity != projector continuity
    pointwise resolvent continuity != uniform contour-integral continuity
    fixed Riesz contour persistence != beta-continuous vacuum
    finite-volume top isolation != uniform thermodynamic mass gap
    uniform finite-volume gap != continuum Yang--Mills mass gap.

These boundaries are part of the theorem architecture, not editorial caveats.
