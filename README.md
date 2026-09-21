# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, finite periodic Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative spatial response, coercivity, and the mass-gap problem.

The repository is intentionally layered. Finite-volume probability, local heat-bath laws, fixed-right response, weighted spatial influence, spectral continuation, coercivity, and continuum targets are kept separate so that a theorem proved in one layer is not silently promoted into a stronger statement in another.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current theorem spine has advanced past the earlier abstract self-consistent-response stage. The actual canonical fixed-right response profile and its exact weighted coefficient are now formalized, the high-temperature half-barrier continuation has been reduced to coordinatewise beta-continuity of the canonical response, and the current work has built the finite-volume spectral continuation machinery needed to prove that continuity.
>
> The immediate open problem is therefore no longer “construct an arbitrary response majorant.” It is to continue the isolated physical top eigenspace in beta, obtain a continuous canonical positive vacuum/top mode, and transport that continuity to the fixed-right kernel-section law and canonical response coordinates.

---

## Repository authority — 2026-09-21 JST

Authoritative theorem-carrier branch:

    formal/real-hilbert-uniform-coercive-strong-limit

Exact theorem-bearing baseline for this documentation refresh:

    295700014db3661c046c3d56f57e6cca809c63c2

This is the merge commit of PR #4613:

    Prove canonical Riesz contour beta stability

Authority order:

    1. exact current GitHub SHA on the authoritative theorem-carrier branch
    2. formal Lean theorem artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

When histories differ, main is not theorem authority.

---

# Current proof spine

    FINITE PERIODIC WILSON / OS ROOT
      -> compact SU(N) finite lattice
      -> reflection-positive / OS carriers
      -> one-slab physical transfer
      -> finite-volume spectral architecture
                                                        [INTEGRATED]

    EXACT ONE-LINK / COVARIANCE MECHANICS
      -> continuous normalized one-link law
      -> conditional expectation / L2 projection
      -> deterministic and random-scan telescopes
      -> fixed-volume covariance remainder -> 0
                                                        [INTEGRATED]

    GENUINE LOCAL SPATIAL THEORY
      -> active-neighbor degree <= 18
      -> base-L1 exponential weights
      -> local Harnack kernel
      -> volume-independent weighted local Green bound
                                                        [INTEGRATED]

    RESPONSE-CONTROLLED FIXED-RIGHT THEORY
      -> canonical response profile R_can
      -> pin-free physical response kernel
      -> response-controlled random-scan recurrence
      -> exact source-forcing sum
      -> terminal removal at fixed volume
                                                        [#4577-#4595]

    AGGREGATE REMOTE / CANONICAL COLUMN CLOSURE
      -> weighted target aggregation without target-cardinality loss
      -> pin-free source-discrepancy superposition
      -> aggregate remote resolvent
      -> canonical weighted remote-column estimate
      -> local C5 exceptional-column estimate
                                                        [#4597-#4603]

    EXACT CANONICAL COEFFICIENT / HALF-BARRIER
      -> exact finite-volume canonical coefficient M_can
      -> M_can supplies its own certificate
      -> M_can <= Phi(M_can) under c_pf(M_can) < 1
      -> M_can(beta=0) = 0
      -> M_can != 1/2 on a volume-independent high-temperature interval
      -> continuity of M_can would imply M_can < 1/2 there
      -> continuity of M_can reduced to coordinatewise response continuity
                                                        [#4604-#4608]

    FINITE-VOLUME SPECTRAL BETA CONTINUATION
      -> top-ray uniqueness
      -> physical transfer Lipschitz in beta
      -> normalized transfer continuous on beta >= 0
      -> complex scalar extension / fixed-z resolvent continuous in beta
      -> fixed canonical Riesz circle persists in nearby resolvent sets
      -> nearby resolvent continuous in z on that fixed contour
                                                        [#4609-#4613]

    CURRENT FRONTIER
      fixed-contour resolvent beta control
        -> beta-continuous Riesz / CFC top projector
        -> continuous normalized positive top vector / vacuum
        -> continuous fixed-right kernel-section law
        -> coordinatewise canonical response beta-continuity
        -> M_can beta-continuity
        -> discharge the #4607 half-barrier continuation
                                                        [OPEN NOW]

    DOWNSTREAM
      strict pin-free weighted physical influence
      -> source-to-target spatial response decay
      -> terminal base-L1 covariance decay
      -> cubic-shell summability / uniform remote residual
      -> strict physical sweep contraction
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic / continuum physical carrier
      -> Clay-level existence + mass gap
                                                        [OPEN]

---

# 1. Fixed-volume covariance mechanics are closed

The finite periodic Wilson / OS architecture and exact one-link conditional-expectation machinery are integrated.

In particular, PRs #4547-#4548 close the fixed-volume covariance remainder along complete random-scan blocks:

    Cov_mu(F, P_scan^(n * L_H) G) -> 0.

This is a fixed-volume statement. It is not by itself a volume-uniform spatial mixing estimate.

---

# 2. The local exponential mechanism is genuinely volume-independent

For

    W_center(x) := s ^ baseL1Distance(center,x),

with s >= 1, the local physical Harnack kernel satisfies a weighted bound with coefficient

    rho_s := 18 * eta(beta) * s^2.

PRs #4559-#4560 prove the iterated local bound and the finite Green estimate under rho_s < 1.

This sparse local mechanism remains the geometric core of the spatial argument.

---

# 3. The fixed-right response object is now canonical

The earlier architecture treated a response profile R as an external nonnegative majorant.

That circularity has been removed.

PR #4583 constructs the actual canonical fixed-right response profile R_can as the pointwise supremum of literal fixed-right target-ratio responses and proves:

    0 <= R_can(target,source) <= exp(16 * beta).

PR #4584 proves its minimality among uniform nonnegative response profiles and connects weighted certificates directly to the canonical object.

PRs #4586-#4595 then remove the obsolete distinguished-target pin from the physical-left response kernel and carry the pin-free coefficient through:

    one-link law variation
      -> random-scan iteration
      -> accumulated source forcing
      -> stationary finite-step response
      -> fixed-volume terminal removal
      -> canonical remote resolvent.

The pin-free weighted coefficient has the form

    c_pf(beta,s,M)
      := 18 * eta(beta) * s^2
         + exp(16 * beta) * M.

No standalone distinguished-target +eta(beta) term remains.

---

# 4. The remote target family is aggregated without volume loss

PRs #4597-#4600 remove the remaining target-cardinality loss.

The exponentially weighted sum of singleton target variations satisfies an exact aggregate identity of the form

    sum_target W_center(target) * V_target(e)
      = exp(16 * beta) * W_center(e),

and the accumulated pin-free source discrepancy is exactly linear under finite target superposition.

This permits the complete remote family to be estimated by one aggregate resolvent before taking the canonical targetwise supremum.

The resulting canonical remote weighted-column estimate is volume-independent in the spatial volume.

---

# 5. The exceptional C5 column is separately controlled

PRs #4601-#4603 prove a volume-independent local comparison for the fixed-right kernel-section law and transport it to the canonical response profile.

The finite C5 exceptional set has cardinality at most 20, and its weighted contribution is bounded by

    20 * s^2 * exp(16 * beta) * eta_R(beta).

This closes the finite exceptional part of the canonical weighted response column without importing the remote resolvent into the local estimate.

---

# 6. The exact canonical weighted coefficient is formalized

PR #4604 combines the exceptional and remote pieces into an explicit bootstrap map Phi.

PR #4605 then defines the actual finite-volume canonical weighted coefficient M_can as the exact finite maximum of source-normalized weighted canonical response columns.

It proves:

    M_can >= 0,

    M_can supplies its own weighted-column certificate,

and, whenever c_pf(beta,s,M_can) < 1,

    M_can <= Phi(beta,s,M_can).

It also proves exactly:

    M_can(beta = 0) = 0.

This is no longer an arbitrary-coefficient bootstrap. The scalar being bootstrapped is the actual canonical response coefficient of the model.

---

# 7. High-temperature closure has been reduced to continuity

PR #4606 constructs a strictly positive volume-independent beta cutoff on which the half-barrier test is strict:

    c_pf(beta,s,1/2) < 1,

    Phi(beta,s,1/2) < 1/2,

and proves that the actual canonical coefficient cannot equal the barrier:

    M_can != 1/2.

PR #4607 proves the continuation principle:

    M_can continuous on the selected beta interval
      + M_can(0) = 0
      + M_can never equals 1/2
      -> M_can < 1/2 throughout the interval.

PR #4608 reduces continuity of M_can to coordinatewise beta-continuity of the canonical fixed-right response profile.

Therefore the present model-facing analytic obligation is sharply localized:

    prove beta-continuity of the canonical fixed-right response coordinates.

---

# 8. The spectral beta-continuity route is integrated through #4613

PR #4609 proves finite-volume uniqueness of the physical top ray. Every physical top eigenvector is a real scalar multiple of the canonical nonnegative top vector.

PR #4610 proves operator-norm Lipschitz continuity in beta of the actual finite-volume physical one-slab transfer and its top-transfer norm.

PR #4611 packages beta >= 0 as a fixed half-line and proves continuity of the normalized physical one-slab transfer, whose top spectral point is fixed at 1.

PR #4612 transports this to the complex physical operator and proves:

    beta -> normalized complex transfer

is operator-norm continuous, and for every fixed spectral parameter z in the base resolvent set,

    beta -> resolvent(S_beta,z)

is continuous at the base beta.

PR #4613 upgrades pointwise persistence to a whole fixed contour. For the canonical Riesz circle chosen at beta0:

    the entire circle remains in resolventSet(S_beta)

for all sufficiently nearby beta.

On that same fixed circle, the nearby resolvent is continuous in the spectral parameter z.

This is precisely the compact-contour input needed for beta-continuity of the Riesz projector.

---

# 9. Immediate next theorem units

The next coherent units are:

1. prove joint or uniform-enough beta control of the resolvent on the fixed beta0 Riesz circle;

2. transport that control through the circle integral and prove beta-continuity of the normalized Riesz projector;

3. identify that moving Riesz projector with the existing CFC top spectral projection at nearby beta;

4. use top-ray uniqueness plus positivity/normalization to select a canonical positive top vector continuously in beta;

5. transport the continuous top vector to the fixed-right ground-state kernel section and normalized fixed-right law;

6. prove coordinatewise beta-continuity of the canonical response profile;

7. apply #4608 and #4607 to obtain the strict high-temperature half-barrier bound for the actual M_can;

8. instantiate the pin-free weighted physical kernel with that strict canonical coefficient and move into spatial decay.

No covariance decay, coercivity, Poincare inequality, or mass-gap statement should be used upstream to prove the continuity steps.

---

# 10. Downstream route after canonical response continuity

Once the continuity premise in #4607 is discharged, the intended route is:

    canonical response continuity
      -> M_can < 1/2 on a nonempty high-temperature interval
      -> strict c_pf(beta,s,M_can) < 1
      -> strict pin-free weighted physical influence
      -> source-to-target spatial response decay
      -> terminal kernel-section base-L1 covariance decay
      -> cubic-shell summability
      -> volume-uniform remote residual
      -> strict physical sweep contraction
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic / continuum physical limit
      -> sufficiently rich nontrivial 4D Yang--Mills state/field
      -> spectral mass gap above the vacuum.

Every arrow remains a separate theorem obligation.

---

# 11. Permanent semantic boundaries

These distinctions are part of the formal proof discipline:

    finite-volume theorem != continuum theorem
    fixed-volume Doeblin rate != volume-uniform physical contraction
    random-scan ergodicity != spatial covariance decay
    covariance identity != covariance decay
    covariance decay != mass gap
    one-link conditional expectation != full Gibbs-law identification
    coarse tagged carrier != actual sparse physical carrier
    local Harnack propagation != remote response closure
    pointwise resolvent continuity != contour-uniform projector continuity
    top-ray uniqueness != beta-continuous vacuum choice
    Riesz contour persistence != completed response continuity
    M_can != 1/2 != M_can < 1/2 without a continuity argument
    finite-volume spectral gap != thermodynamic/continuum Yang--Mills mass gap.

No sorry, admit, new axioms, hidden constants, hypothesis weakening, theorem weakening, or semantic broadening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean v4.30.0-rc2 with the repository-pinned mathlib revision.

Recent spectral-continuity work also makes explicit local instances where needed to avoid generated-instance/import-diamond ambiguity under this pinned toolchain.

Repository lockfiles and the exact current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Integrated through PR #4613:** fixed-volume covariance-remainder closure; volume-independent local weighted Harnack theory; canonical fixed-right response profile; pin-free response-controlled physical kernel; exact source-forcing recurrence and fixed-volume terminal removal; aggregate remote-family control without target-cardinality loss; exceptional C5 weighted-column control; exact canonical weighted coefficient M_can and its bootstrap map; high-temperature half-barrier exclusion and continuation theorem conditional on response continuity; top-ray uniqueness; beta-Lipschitz physical transfer; normalized transfer continuity; complex fixed-z resolvent continuity; and nearby persistence of the full canonical Riesz contour.

**Open now:** prove beta-continuity of the Riesz/CFC top projector, construct a beta-continuous canonical positive vacuum/top mode, transport it to the fixed-right kernel-section law and canonical response coordinates, discharge the M_can continuity premise, and then enter strict weighted spatial decay and the downstream coercivity/gap program.
