# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, finite periodic Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, conditional expectation, quantitative spatial response, coercivity, and the mass-gap problem.

The repository is intentionally layered. Finite-volume probability, local heat-bath laws, fixed-right response, weighted spatial influence, local spectral continuation, volume-uniform coercivity, thermodynamic limits, and continuum targets are kept separate so that a theorem proved in one layer is not silently promoted into a stronger statement in another.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The finite-volume program has moved substantially beyond the earlier abstract response-majorant stage. The actual canonical fixed-right response profile and exact weighted coefficient are formalized, the high-temperature half-barrier has been reduced to continuity of the canonical response coordinates, and the spectral continuation route now includes a beta-continuous fixed-contour Riesz continuation, a rank-one canonical complex top sector, bilateral absorption of the nearby canonical top projector, and local idempotence of the fixed-contour continuation.
>
> The immediate open problem is to prove rank-one persistence for that nearby fixed-contour idempotent and identify it with the canonical CFC top projector at the moving coupling. Only after that identification is it legitimate to promote fixed-contour continuity to continuity of the canonical moving top projector and then construct a continuous canonical positive top mode.

---

## Repository authority — 2026-09-22 JST

Authoritative theorem-carrier branch:

    formal/real-hilbert-uniform-coercive-strong-limit

Exact theorem-bearing mathematical baseline for this documentation refresh:

    30d54b17c3d1a9b7e243c4079e18e533d2e070c9

This is the merge commit of PR #4625:

    Prove fixed-contour Riesz projector idempotence

Documentation-only commits after this SHA do not change the theorem-bearing mathematical baseline.

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
      -> exact source-forcing recurrence
      -> fixed-volume terminal removal
      -> aggregate remote-family closure
      -> local C5 exceptional-column control
                                                        [#4577-#4603]

    EXACT CANONICAL COEFFICIENT / HALF-BARRIER
      -> exact finite-volume coefficient M_can
      -> self-certificate and bootstrap map Phi
      -> M_can(beta=0) = 0
      -> M_can != 1/2 on a positive high-temperature interval
      -> continuity would imply M_can < 1/2
      -> M_can continuity reduced to response-coordinate continuity
                                                        [#4604-#4608]

    FINITE-VOLUME SPECTRAL CONTINUATION
      -> top-ray uniqueness
      -> physical transfer Lipschitz in beta
      -> normalized complex transfer continuous in beta
      -> fixed-z resolvent continuous in beta
      -> canonical beta0 Riesz circle persists nearby
                                                        [#4609-#4613]

    FIXED-CONTOUR RIESZ CONTINUATION
      -> fixed beta0 contour projector Q_beta is beta-continuous
      -> Q_beta0 equals canonical CFC top projector P_beta0
      -> canonical complex top sector is rank one
      -> Q_beta absorbs nearby canonical P_beta on both sides
      -> local radial resolvent margin / contour deformation
      -> separated-circle Fubini and Cauchy-kernel calculus
      -> separated-circle double-resolvent identity
      -> Q_beta^2 = Q_beta for beta near beta0
                                                        [#4616-#4625]

    CURRENT FRONTIER
      Q_beta idempotent + Q_beta -> P_beta0 in norm
        + rank(P_beta0)=1
        + bilateral absorption of P_beta
        -> rank-one persistence for Q_beta
        -> identify Q_beta = P_beta
        -> canonical moving top projector beta-continuity
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

# 1. Canonical response closure through the half-barrier reduction

The finite-volume Wilson / OS architecture, one-link conditional expectation machinery, fixed-volume covariance-remainder closure, local volume-independent Harnack theory, canonical fixed-right response profile, and pin-free response-controlled recurrence are integrated.

The actual canonical weighted coefficient M_can is no longer an auxiliary unknown. PRs #4604-#4605 define the exact finite maximum and prove

    M_can >= 0,

    M_can supplies its own canonical weighted-column certificate,

    c_pf(beta,s,M_can) < 1
      -> M_can <= Phi(beta,s,M_can),

and exactly

    M_can(beta=0) = 0.

PRs #4606-#4608 prove the high-temperature half-barrier architecture:

    M_can != 1/2

on a strictly positive volume-independent beta interval, and

    continuity of M_can
      + M_can(0)=0
      + exclusion of M_can=1/2
      -> M_can < 1/2.

The remaining input is model-facing: continuity of the canonical fixed-right response coordinates.

---

# 2. Spectral beta continuation through the fixed contour

PR #4609 proves finite-volume uniqueness of the real physical top ray.

PR #4610 proves operator-norm Lipschitz continuity in beta of the genuine finite-volume physical one-slab transfer and its top norm.

PR #4611 normalizes the transfer on beta >= 0 and fixes the top spectral point at 1.

PR #4612 passes to the genuine same-root complex physical carrier and proves operator-norm continuity of the normalized complex transfer, together with fixed-spectral-parameter resolvent continuity.

PR #4613 upgrades pointwise persistence to the whole canonical beta0 Riesz circle:

    for beta sufficiently near beta0,
      sphere(1,r_beta0) subset resolventSet(S_beta).

This supplies the fixed contour used by the subsequent continuation argument.

---

# 3. Fixed-contour Riesz projector continuity is proved

PR #4616 defines the normalized Riesz projector on the fixed beta0 canonical contour:

    Q_beta
      := (2*pi*i)^(-1)
         * integral_{|z-1|=r_beta0} resolvent(S_beta,z) dz.

It proves operator-norm continuity

    Q_beta -> Q_beta0

as beta -> beta0, using joint resolvent continuity, compactness of the fixed circle, uniform contour control, and the circle-integral norm estimate.

At the base coupling,

    Q_beta0 = P_beta0,

where P_beta0 is the existing canonical CFC top spectral projection.

Important boundary:

    fixed-contour continuity of Q_beta
      != continuity of the moving canonical projector P_beta

until nearby equality Q_beta = P_beta is proved.

---

# 4. The finite-volume complex top sector is rank one

PR #4617 identifies the real normalized-transfer top eigenspace with the real span of the canonical nonnegative top vector, transports the statement through the genuine complex physical carrier, and proves that the canonical complex CFC top projection has one-dimensional range.

Thus, at every fixed finite volume and nonnegative beta,

    range(P_beta)

is the canonical complex top line.

This is a finite-volume rank-one theorem. It is not a thermodynamic or continuum spectral-gap statement.

---

# 5. The fixed contour absorbs the nearby canonical top sector

PR #4618 proves, for beta sufficiently near beta0,

    Q_beta * P_beta = P_beta,

    P_beta * Q_beta = P_beta.

This is a strong local relation between the fixed-contour continuation and the actual nearby canonical CFC top projector.

It does not by itself prove

    Q_beta = P_beta.

The missing ingredient is control of the rank/range of Q_beta.

---

# 6. Local contour calculus for idempotence is integrated

PRs #4619-#4624 build the analytic infrastructure needed to prove idempotence without assuming continuity of the excited-sector gap:

- a pointwise two-resolvent identity;
- compact radial spectral separation and a protected resolvent annulus;
- contour-radius deformation inside that annulus;
- a pinned-mathlib Fubini backport for nested interval/circle integrals;
- exterior- and interior-pole Cauchy-kernel identities;
- separated-circle parameter integrability;
- the separated-circle double-resolvent identity.

This route deliberately stays pointwise on the physical Hilbert space when operator-valued integrals are evaluated, avoiding unnecessary operator-algebra instance search.

---

# 7. Fixed-contour Riesz idempotence is proved

PR #4625 closes the local algebraic projector property:

    for beta sufficiently near beta0,
      Q_beta * Q_beta = Q_beta.

The proof uses only:

    persistence of the fixed beta0 contour,
    a local radial resolvent margin,
    contour deformation,
    separated inner/outer circles,
    the resolvent identity,
    Fubini,
    Cauchy-kernel evaluation.

It does not use continuity of the nearby excited-sector gap and does not assume Q_beta = P_beta.

This is the current theorem-bearing endpoint.

---

# 8. Immediate next theorem units

The next coherent units are:

1. combine Q_beta^2 = Q_beta, Q_beta -> P_beta0 in operator norm, and rank(P_beta0)=1 to prove that the range of Q_beta is at most one-dimensional for beta sufficiently near beta0;

2. use bilateral absorption of the nonzero rank-one P_beta to show that Q_beta is nonzero and hence exactly rank one;

3. conclude from range inclusion and rank one that Q_beta = P_beta;

4. combine that local equality with PR #4616 to obtain beta-continuity of the canonical moving CFC top projector;

5. use top-ray uniqueness, positivity, and normalization to construct a continuous canonical positive top vector;

6. transport that vector to the fixed-right ground-state kernel-section law and normalized fixed-right law;

7. prove coordinatewise beta-continuity of R_can;

8. apply #4608 and #4607 to obtain the strict high-temperature half-barrier bound for the actual M_can;

9. instantiate the strict pin-free weighted physical kernel and enter spatial response decay.

No covariance decay, coercivity, Poincare inequality, or mass-gap statement should be used upstream to prove these local continuity steps.

---

# 9. Downstream route after canonical response continuity

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

# 10. Permanent semantic boundaries

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
    fixed-contour Riesz continuity != moving canonical-projector continuity
    top-ray uniqueness != beta-continuous vacuum choice
    rank-one P_beta != rank-one Q_beta without persistence
    Q_beta^2 = Q_beta != Q_beta = P_beta
    bilateral absorption != projector equality without range/rank control
    Riesz contour persistence != completed response continuity
    M_can != 1/2 != M_can < 1/2 without continuity
    finite-volume top isolation != volume-uniform thermodynamic gap
    uniform finite-volume gap != continuum Yang--Mills mass gap.

No sorry, admit, new axioms, hidden constants, hypothesis weakening, theorem weakening, or semantic broadening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean v4.30.0-rc2 with the repository-pinned mathlib revision.

Recent contour work intentionally uses pinned-compatible APIs rather than assuming newer Mathlib theorem names. Several proofs make type information explicit to avoid expensive or ambiguous operator-algebra instance inference.

Repository lockfiles and the exact current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Integrated through PR #4625:** fixed-volume covariance-remainder closure; volume-independent local weighted Harnack theory; canonical fixed-right response profile; pin-free response-controlled recurrence; aggregate remote-family closure; exceptional C5 control; exact canonical coefficient M_can; half-barrier exclusion and continuation architecture; finite-volume top-ray uniqueness; physical-transfer beta continuity; complex fixed-z resolvent continuity; fixed canonical Riesz-circle persistence; fixed-contour Riesz-projector beta continuity; rank-one complex canonical top sector; bilateral fixed-contour absorption of the nearby canonical top projector; local radial contour deformation; separated-circle Fubini/Cauchy calculus; separated-circle double-resolvent identity; and fixed-contour Riesz idempotence.

**Open now:** prove rank-one persistence of the nearby fixed-contour idempotent, identify it with the moving canonical CFC top projector, obtain canonical projector and positive-vacuum beta continuity, transport that continuity to the fixed-right response coordinates, discharge the M_can continuity premise, and then enter strict weighted spatial decay and the downstream coercivity/gap program.
