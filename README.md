# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, finite periodic Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative mixing, spatial influence, coercivity, and the mass-gap problem.

The repository is intentionally layered. Finite-volume probability, one-link laws, spatial response, covariance identities, weighted kernels, coercivity, spectral statements, and continuum targets are kept separate so that a theorem proved in one layer is not silently promoted into a stronger statement in another.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current formalization has advanced beyond the earlier weighted-local/remote split. It now contains a response-controlled finite-step random-scan route that keeps the genuine physical left kernel separate from the represented right-boundary forcing.
>
> The immediate open problem is to turn that route into a **non-circular, volume-independent self-consistent fixed-right response bound**, and from it derive an explicit exponentially weighted remote coefficient `kappa_s(beta,s)` satisfying a strict absorption condition.

---

## Repository authority — theorem baseline 2026-09-20 JST

Authoritative theorem-carrier branch:

    formal/real-hilbert-uniform-coercive-strong-limit

Exact theorem-bearing baseline for this documentation refresh:

    e56ea50823fb70d6fb6f50e33ae79ea2a9d9ac01

This is the merge commit of PR #4575:

    Iterate response-controlled random-scan recurrence

This README/ROADMAP refresh is documentation-only. If the docs PR merges before another theorem PR, the branch pointer will advance while the theorem-bearing mathematical baseline remains the merge above.

Authority order:

    1. exact current GitHub SHA on the authoritative theorem-carrier branch
    2. formal Lean theorem artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

`main` is not theorem authority when histories differ.

---

# Current proof spine

    FINITE PERIODIC WILSON / OS ROOT
      -> compact SU(N) finite lattice
      -> reflection-positive / OS carriers
      -> one-slab transfer / ground-state architecture
      -> coercivity / spectral routing
                                                        [INTEGRATED]

    CONTINUOUS ONE-LINK LAW + LOCAL GEOMETRY
      -> normalized continuous SU(N) fiber law
      -> measurable heat-bath reinsertion
      -> stationarity / represented-source cancellation
      -> active-neighbor degree <= 18
      -> C5 exceptional geometry
                                                        [INTEGRATED]

    EXACT KERNEL-SECTION / COVARIANCE MECHANICS
      -> one-link conditional expectation
      -> L2 projection / fluctuation identities
      -> deterministic and restricted-random-scan telescopes
      -> finite covariance resolvent
                                                        [INTEGRATED]

    FIXED-VOLUME COVARIANCE-REMAINDER CLOSURE
      -> complete-block Doeblin contraction
      -> exact block/step bridge
      -> Cov(F, P_scan^(n * L_H) G) -> 0
                                                        [#4547-#4548]

    COARSE TAGGED RANDOM-SCAN ROUTE
      -> eligible-coordinate pullback
      -> fixed-volume geometric resolvent
      -> auxiliary unscanned response
      -> represented fixed-right finite-step/asymptotic response
                                                        [#4551-#4558]

    GENUINE LOCAL EXPONENTIAL THEORY
      -> W_center(x) = s^baseL1Distance(center,x)
      -> rho_s = 18 * eta(beta) * s^2
      -> K_local W <= rho_s W
      -> K_local^d W <= rho_s^d W
      -> G_local,M W <= (1-rho_s)^(-1) W
                                                        [#4559-#4560]

    FIXED-TARGET / REMOTE WEIGHTED REFINEMENT
      -> exact local + distinguished-target pin + remote decomposition
      -> exponential absorption of the local/pin contribution
      -> weighted response bootstrap interfaces
      -> heat-bath variation propagation through fixed-target envelope
      -> fixed-target physical tagged carrier
                                                        [#4563-#4569]

    REMOTE-RESPONSE LINEARIZATION
      -> optional uniform remote certificate isolated as an interface
      -> weighted random-scan superposition
      -> remote residual <= exp(16 beta) * fixed-right response profile
      -> actual fixed-target envelope <= response-controlled kernel K_R
                                                        [#4570-#4573]

    RESPONSE-CONTROLLED RANDOM-SCAN DYNAMICS
      -> one actual random-scan step propagates left variation by K_R
      -> represented right-source forcing kept separate
      -> v_(n+1) = Q_R v_n
      -> d_(n+1) = averaged[d_n + cross-boundary forcing(v_n)]
      -> n-step physical left variation <= v_n
      -> n-step boundary-source discrepancy <= d_n
                                                        [#4574-#4575]

    CURRENT FRONTIER
      construct R from the actual fixed-right response itself and prove
      a self-consistent weighted inequality strong enough to solve for R,
      hence derive

        R_remote,weighted(center,source)
          <= kappa_s(beta,s) * W_center(source)

      with a concrete volume-independent coefficient and a nonempty regime

        18 * eta(beta) * s^2
          + eta(beta)
          + kappa_s(beta,s)
          < 1.
                                                        [OPEN NOW]

    DOWNSTREAM
      strict weighted physical influence
      -> terminal kernel-section base-L1 covariance decay
      -> cubic shell summability
      -> volume-uniform remote residual
      -> strict physical sweep gate
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic / continuum physical carrier
      -> sufficiently rich 4D Yang--Mills field/state
      -> Clay-level existence + mass gap
                                                        [OPEN]

---

# 1. Fixed-volume covariance remainder is closed

The restricted-random-scan covariance telescope contains a remainder

    Cov_mu(F, P_scan^M G).

PR #4547 identifies complete-block evolution with the original random-scan iterate at complete-block times:

    P_block^n f
      = P_scan^(n * L_H) f.

PR #4548 combines this with the fixed-volume Doeblin limit and proves

    Cov_mu(F, P_scan^(n * L_H) G) -> 0.

This closes the finite-volume covariance remainder. It does **not** give a volume-uniform mixing constant or a spatial correlation length.

---

# 2. The coarse tagged carrier remains a fixed-volume tool

PRs #4551-#4557 construct an explicit restricted-random-scan resolvent for the coarse tagged carrier.

The exact physical eligible-row coefficient contains

    (card(Link) - 1) * DistinctFiberOffFiberInfluence(beta),

so the dense left-left tagged mechanism worsens with spatial volume. It is therefore useful for finite-volume response identities and comparison arguments, but it is not the final spatial-decay mechanism.

PR #4558 transports the asymptotic fixed-right response back to the actual source-aligned remote physical residual while retaining the real C5 support.

---

# 3. The genuine local Harnack mechanism is volume-independent

For

    W_center(x)
      := s ^ baseL1Distance(center,x),

with `s >= 1`, PR #4559 proves the weighted local Schur bound

    K_local W
      <= rho_s W,

where

    rho_s
      := 18 * eta(beta) * s^2.

PR #4560 iterates it:

    K_local^d W
      <= rho_s^d W,

and, under

    rho_s < 1,

proves the finite local Green/resolvent estimate

    G_local,M W
      <= (1-rho_s)^(-1) W.

This local mechanism is sparse, geometric, and volume-independent.

---

# 4. Fixed-target weighted structure is now explicit

The post-#4561 work sharpened the weighted decomposition at the actual fixed-target law level.

PR #4563 connects the weighted remote column to the local Harnack resolvent structure.

PR #4564 decomposes the fixed-target physical envelope into:

    local Harnack contribution
      + distinguished-target pin
      + actual source-aligned remote residual.

PR #4565 absorbs the distinguished-target Harnack pin into the exponential-weight bookkeeping.

PR #4566 lifts the fixed-target decomposition into a weighted response-bootstrap interface.

PRs #4567 and #4568 make the influence estimate scale correctly with an arbitrary nonnegative variation profile and propagate that variation through the actual one-link heat-bath update.

PR #4569 packages the resulting fixed-target physical structure into a tagged carrier suitable for subsequent random-scan algebra.

The important point is that these results still retain the actual physical fixed-target structure rather than replacing it with the old dense all-to-all coefficient.

---

# 5. Remote residual is linearized through fixed-right response

PR #4570 introduces a **uniform remote residual certificate** only as an algebraic interface. It does not assert that the certificate exists.

If a coefficient `kappa` is supplied, the corresponding full weighted coefficient is

    18 * eta(beta) * s^2
      + eta(beta)
      + kappa.

The extra `eta(beta)` is the distinguished-target pin.

PR #4571 adds weighted superposition machinery needed to transport target-dependent weights through variation profiles.

PR #4572 proves the crucial carrier-free linearization:

    actual weighted remote residual
      <= exp(16 * beta)
         * weighted mass of a fixed-right response profile.

This removes the need to use the coarse random-scan left-left transport when estimating the actual remote residual.

---

# 6. The actual fixed-target envelope is response-controlled

Let `R(target,source)` be a nonnegative profile satisfying a uniform bound on the actual fixed-right target-ratio response.

PR #4573 defines a configuration-independent physical kernel `K_R` whose entries are:

    diagonal:
      0

    C5/local exceptional term:
      eta(beta)

    remote term:
      exp(16 * beta) * R(target,source).

It proves that the actual configuration-dependent fixed-target envelope is bounded by `K_R`, and transports this domination to the actual one-link law and variation estimates.

This is a decisive change in architecture:

    old route:
      actual physical update
        -> coarse all-to-all tagged left-left carrier

    current route:
      actual physical update
        -> response-controlled physical kernel K_R.

The price is that `R` is not yet constructed self-consistently. That is now the central analytic problem.

---

# 7. Response-controlled random scan is integrated through finite step

PR #4574 proves that one actual restricted random-scan step propagates physical left variation through the response-controlled kernel.

If `v` is the current left variation profile, define schematically

    v_next = Q_R v.

The represented right-boundary source effect is kept separate as

    CrossBoundaryRandomScanSourceForcing(source,v).

This prevents the volume-growing coarse left-left tagged coefficient from contaminating the spatial recurrence.

PR #4575 iterates this structure.

Define

    v_0 = initial variation
    v_(n+1) = Q_R v_n.

Then every actual `n`-step restricted-random-scan observable has left-fiber variation bounded by `v_n`.

In parallel, define a scalar source discrepancy

    d_0 = 0

and one-step recurrence

    d_(n+1)
      = average_fiber [
          d_n
          + CrossBoundaryBoundedTestMajorant(beta,fiber,source)
            * v_n(fiber)
        ].

PR #4575 proves that the difference between two represented right-boundary-value random-scan orbits is bounded pointwise by `d_n`.

The augmented coarse tagged carrier is used only as an algebraic proof device for the right-source affine identity. Its dense left-left block is not used as the spatial propagation mechanism.

---

# 8. The current open theorem is now a self-consistent response closure

The immediate task is no longer merely “assume a remote weighted coefficient.”

The route has been sharpened to:

    actual fixed-right response
      -> define/majorize a response profile R
      -> response-controlled kernel K_R
      -> finite-step left variation v_n
      -> accumulated right-source discrepancy d_n
      -> stationary/asymptotic fixed-right response inequality
      -> weighted scalar/profile bootstrap
      -> explicit bound on R
      -> #4572 remote-residual linearization
      -> concrete kappa_s(beta,s).

The target is a theorem of the schematic form

    weighted_mass(R)
      <= A(beta,s)
         + B(beta,s) * weighted_mass(R),

with

    B(beta,s) < 1,

so that

    weighted_mass(R)
      <= A(beta,s) / (1-B(beta,s)).

That bound should then imply

    R_remote,weighted(center,source)
      <= kappa_s(beta,s) * W_center(source),

with `kappa_s` independent of the periodic spatial volume.

No terminal covariance decay, physical sweep contraction, Poincare/coercivity, or mass-gap statement may be used upstream to obtain this closure.

---

# 9. Next concrete proof units

The next natural Lean units are:

1. normalize the one-step source discrepancy exactly as

       d_next
         = d + CrossBoundaryRandomScanSourceForcing(source,v),

   using positivity/nonemptiness of the spatial-link finite type;

2. derive the finite-sum representation

       d_n
         = sum_{j < n}
             CrossBoundaryRandomScanSourceForcing(source,v_j);

3. transport stationarity/fixed-right response to the response-controlled finite-step recurrence, replacing the old coarse left-left propagation;

4. bound the terminal finite-step discrepancy under a strict weighted norm condition on `K_R`;

5. pass to an asymptotic self-consistent fixed-right response inequality;

6. solve that inequality in exponential weight and obtain an explicit response profile bound;

7. feed the result through PR #4572 to derive the actual remote coefficient `kappa_s`;

8. instantiate the #4570 absorption interface and prove a nonempty regime with

       18 * eta(beta) * s^2
         + eta(beta)
         + kappa_s(beta,s)
         < 1.

Only after these steps should the proof move into terminal covariance decay.

---

# 10. Downstream route after self-consistent weighted closure

Once the full physical weighted influence is strictly subinvariant:

    strict weighted physical influence
      -> source-to-target response decay
      -> terminal kernel-section base-L1 covariance decay
      -> cubic shell summability
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
    local Harnack propagation != remote residual control
    fixed-right response interface != proof of a self-consistent response bound
    response-controlled kernel K_R != construction of R
    uniform remote certificate != proof that the certificate exists
    weighted local resolvent != weighted remote closure
    strict finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

No `sorry`, `admit`, new axioms, hidden constants, hypothesis weakening, theorem weakening, or semantic broadening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean `v4.30.0-rc2` with the repository-pinned mathlib revision. Repository lockfiles and the exact current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Integrated through PR #4575:** fixed-volume covariance-remainder closure; fixed-volume coarse tagged response resolvent; volume-independent local Harnack weighted resolvent; fixed-target local/pin/remote decomposition; weighted response bootstrap interfaces; variation-scaled one-link propagation; weighted superposition; linearization of the actual remote residual through fixed-right response; response-controlled physical kernel `K_R`; one-step actual random-scan propagation by `K_R`; and finite-step iteration of both the left variation profile and represented right-source discrepancy.

**Open now:** construct and solve the self-consistent fixed-right response inequality in exponential weight, derive a concrete volume-independent `kappa_s(beta,s)`, prove strict full weighted subinvariance, and only then continue to terminal spatial covariance decay, the uniform remote-residual pipeline, coercivity, a uniform spectral gap, and the thermodynamic/continuum Yang--Mills construction.
