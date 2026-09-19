# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Exact finite-volume statements, continuous one-link laws, ground-state kernel-section probability laws, sparse/local influence estimates, covariance identities, geometric shell bounds, and continuum/OS targets are kept separate so that a finite-volume or conditional theorem is never silently promoted into a continuum mass-gap theorem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> At the current continuous `SU(N)` frontier, the model-specific remote conditional-law influence, physical local-plus-remote envelope, uniform-residual reduction, base-`L1` shell geometry, remote kernel-section conditional expectation, one-link covariance/Dirichlet identities, deterministic-schedule covariance telescope, and restricted-random-scan finite-resolvent telescope are all formalized.
>
> The remaining analytic obstruction has been narrowed to **volume-uniform spatial decay of the exact ground-state kernel-section covariance** appearing in the two-step terminal normal form. The current finite resolvent theorem does not itself prove that the covariance remainder vanishes or decays exponentially.

---

## Repository authority — documentation baseline 2026-09-19 JST

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing commit used for this documentation refresh is:

    7184acd5f19fc5dc1d2e4b5f6774e7c3958ea805

This is the merge commit of PR #4513:

    Telescope restricted random-scan covariance through finite resolvent

This README/ROADMAP refresh is docs-only. After the docs PR merges, the branch pointer will advance while the theorem-bearing mathematical baseline remains PR #4513 until a later theorem PR lands. Always fresh-fetch the theorem-carrier branch before theorem work.

Authority order:

    1. exact current GitHub SHA on the authoritative theorem-carrier branch
    2. formal Lean artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

`main` is a public landing surface and infrastructure branch; it is not theorem authority when histories differ.

---

# Current proof spine

    FINITE PERIODIC WILSON / OS ROOT
      -> compact SU(N) Wilson model
      -> reflection-positive / OS carriers
      -> one-slab transfer and ground-state structure
      -> coercivity / spectral routing
                                                        [INTEGRATED]

    CONTINUOUS C5 ONE-LINK LAW + LOCAL GEOMETRY
      -> normalized continuous SU(N) fiber law
      -> measurable heat-bath reinsertion
      -> represented-source cancellation
      -> active-neighbor degree <= 18
      -> C5 exceptional set <= 20
                                                        [INTEGRATED]

    FIXED-RIGHT RESPONSE + REMOTE CROSS-RATIO CONTROL
      -> kernel-section probability law
      -> target-ratio response
      -> targetwise worst-case cross-ratio majorant
      -> actual remote bounded-test conditional influence
                                                        [INTEGRATED #4442-#4469]

    PHYSICAL LOCAL + REMOTE ENVELOPE
      -> physical left influence <= active Harnack + remote residual
      -> source-aligned residual kernel
      -> finite-volume residual maximum
      -> physical envelope random-scan contraction under a strict gate
                                                        [INTEGRATED #4470-#4478]

    UNIFORM REMOTE-RESIDUAL REDUCTION
      -> abstract uniform residual certificate
      -> two-step terminal envelope
      -> spatial-shell summability
      -> explicit crossing denominator floor
      -> cubic base-L1 shell bound and summability
                                                        [INTEGRATED #4479-#4494]

    REMOTE KERNEL-SECTION CONDITIONAL EXPECTATION
      -> actual one-link conditional law = off-fiber conditional expectation
      -> one-link stationarity
      -> L2 projection carrier
      -> covariance self-adjointness
      -> fluctuation symmetry / idempotence / orthogonal decomposition
      -> one-link covariance Dirichlet identity
                                                        [INTEGRATED #4495-#4506]

    COVARIANCE TELESCOPES
      -> deterministic one-link schedule telescope
      -> local fiber-variation decrement bound
      -> tagged schedule bound
      -> restricted random-scan covariance Dirichlet identity
      -> iterated restricted-scan transport
      -> normalized finite resolvent profile
      -> finite covariance remainder <= variation/resolvent pairing
                                                        [INTEGRATED #4507-#4513]

    CURRENT ANALYTIC FRONTIER
      exact terminal kernel-section covariance
      -> prove base-L1 exponential decay, uniformly in periodic volume
      -> feed cubic shell summability
      -> obtain explicit uniform remote residual rho
      -> close strict physical sweep gate
                                                        [OPEN NOW]

    DOWNSTREAM
      uniform physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic/scaling-limit physical carrier
      -> sufficiently rich 4D Yang--Mills field/state
      -> Clay-level existence + mass gap
                                                        [OPEN]

---

# 1. Model-specific remote conditional influence is now closed

PRs #4464, #4467, and #4469 completed the normalization step that was still open in the previous documentation baseline.

For a geometrically remote physical target/source pair, the actual normalized one-link conditional-law bounded-test difference is controlled by the targetwise worst-case transformed cross-ratio majorant. Summing those targetwise majorants introduces no remote-cardinality penalty and yields a concrete nonnegative remote residual kernel.

Schematically:

    actualRemoteInfluence(target, source)
      <= WorstCaseCrossRatioInfluenceMajorant(target, source)

and

    sum_remote actualRemoteInfluence
      <= exp(16*beta) * arbitraryStepAggregateTransport.

This is an actual conditional-law theorem. It is no longer merely a fixed-right response or cross-ratio statement.

---

# 2. Physical left influence has a local-plus-remote envelope

PRs #4470-#4478 constructed the physical sparse/local envelope.

The source-aligned physical influence is bounded by:

    active-neighbor Harnack contribution
    + source-aligned remote vacuum residual.

The intrinsic active-neighbor geometry contributes at most 18 terms. The exact finite-volume remote residual maximum is packaged separately, yielding a concrete finite-volume envelope column coefficient of the form:

    18 * eta(beta) + remoteResidualMaximum(H, A).

Under strictness of that finite-volume coefficient, the physical envelope random scan contracts. This is a genuine finite-volume theorem, but the remote maximum is not yet known to be uniformly bounded in `H` by a small enough scalar.

Important boundary: the older dense distinct-fiber coefficient remains a coarse carrier and must not be substituted for the sparse/local physical envelope.

---

# 3. Uniform residual closure has been reduced to one terminal covariance decay statement

PRs #4479-#4494 reorganized the uniformity problem.

The repository now contains:

    RemoteResidualUniformBound(N, beta, rho)

as an explicit proposition, together with theorems reducing it to a two-step terminal envelope. The terminal response is exposed as one covariance divided by a positive crossing expectation, and the denominator has the volume-independent floor:

    crossingExpectation >= exp(-2 * beta).

Hence the terminal response is bounded by:

    exp(2 * beta) * |kernelSectionCovariance|.

The geometric side is already closed. The source-aligned remote base-`L1` shell has the uniform polynomial bound:

    shellCard(r) <= 3 * (2*r + 1)^3.

For every `0 <= q < 1`, the cubic shell majorant times `q^r` is summable. Therefore **no artificial condition such as `18*q < 1` is needed** for terminal shell summability.

The remaining analytic predicate is precisely an exponential base-`L1` bound for the exact ground-state kernel-section covariance:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^(baseL1Distance(target, source))

with constants independent of periodic volume and `0 <= q < 1`.

Once this is proved, the existing cubic-shell theorem produces an explicit uniform `rho`, which feeds the existing physical envelope sweep theorem.

---

# 4. Remote kernel-section one-link updates are actual conditional expectations

PRs #4495-#4506 built the measure-theoretic projection layer needed to attack that covariance.

For geometrically remote target/source pairs, the actual remote kernel-section one-link heat-bath projection is identified almost everywhere with conditional expectation onto the off-fiber sigma-algebra.

The formal consequences now include:

    * stationarity of the kernel-section law under the one-link update;
    * preservation of `MemLp 2`;
    * covariance self-adjointness;
    * fluctuation `Q = I - P` in `L2`;
    * projection idempotence almost everywhere;
    * annihilation of the projected fluctuation;
    * covariance orthogonal decomposition;
    * one-link covariance Dirichlet identity.

No Gibbs-law identification is used in this layer. The object is the exact ground-state kernel-section probability law.

---

# 5. Covariance now telescopes through deterministic schedules and restricted random scan

PRs #4507-#4513 turn the one-link identities into finite multi-step covariance control.

For deterministic schedules, covariance decrements telescope and each decrement is bounded by local fiber variations propagated through the tagged variation carrier.

For physical restricted random scan, the repository now has:

    * the exact one-step covariance Dirichlet identity;
    * preservation of strong measurability and `MemLp 2` through finite iterates;
    * propagation of observable fiber variation by the tagged restricted-scan iterate;
    * a normalized finite restricted-scan resolvent profile;
    * an exact finite covariance telescope;
    * a finite remainder bound by a variation/resolvent pairing.

The key PR #4513 bound is schematic:

    |Cov(F,G) - Cov(F, P_scan^M G)|
      <= sum_fiber variationF(fiber) * finiteResolvent_M(variationG)(fiber).

This is a finite-volume, finite-`M` statement. It does **not** prove:

    P_scan^M G -> constant,
    the covariance remainder -> 0,
    exponential spatial covariance decay,
    a uniform spectral gap.

Those are the next analytic obligations.

---

# 6. Why the current frontier is not a simple total-variation contraction

The literal distinct-fiber C5 carrier has the exact left-column sum:

    (card Link - 1) * offFiberInfluence(beta),

so using that dense carrier directly destroys volume uniformity.

The physical sparse envelope avoids that problem by separating:

    local active-neighbor influence
    from
    remote vacuum-correlation residual.

Therefore the next proof must preserve spatial information. Collapsing all propagated variation to a global total too early would lose the base-`L1` decay needed by the cubic-shell route.

The intended next bridge is spatially weighted: use the kernel-section covariance telescope together with the sparse physical envelope and the already-proved base-`L1` geometry to derive a pointwise covariance decay estimate.

---

# 7. Immediate theorem-development frontier

The next coherent theorem units are:

    1. identify explicit variation profiles for the source crossing observable
       and the two-step terminal observable under the exact kernel-section law;

    2. dominate one-link / restricted-scan propagation by a spatially sparse
       physical influence carrier without replacing the fixed-target law by a
       source-aligned law;

    3. derive a distance-sensitive Green/resolvent estimate rather than only
       an unweighted total-mass estimate;

    4. prove the kernel-section covariance base-L1 exponential-decay predicate
       isolated in PR #4493;

    5. invoke the already-proved cubic shell bridge (#4494) to obtain a
       volume-uniform remote residual scalar rho;

    6. establish a strict physical gate and instantiate the uniform full-sweep
       contraction;

    7. continue to physical Poincare/coercivity and a uniform finite-volume
       transfer/Hamiltonian gap.

---

# 8. Permanent semantic boundaries

These distinctions are part of the proof discipline:

    finite-volume theorem != continuum theorem
    one-link conditional expectation != full Gibbs-law identification
    covariance identity != covariance decay
    covariance decay != mass gap
    variation propagation != correlation decay automatically
    graph-distance shell != base-L1 shell
    exponential graph-shell bound != polynomial base-L1 shell bound
    fixed-right response != actual physical influence
    source-summed residual != volume-uniform residual
    finite resolvent != infinite resolvent / vanishing remainder
    strict finite-volume envelope gate != uniform-in-volume gate
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap

No `sorry`, `admit`, new axioms, hidden constants, weakened hypotheses, or theorem weakening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean `v4.30.0-rc2` with the repository-pinned mathlib revision. The exact repository lockfiles and current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Closed:** actual remote conditional influence, physical local/remote envelope, finite-volume physical sweep carrier, uniform-residual reduction, terminal covariance normal form and denominator floor, polynomial base-`L1` shell geometry, kernel-section conditional expectation, `L2` projection/Dirichlet identities, deterministic and restricted-random-scan covariance telescopes.

**Open now:** prove volume-uniform base-`L1` exponential decay of the exact terminal kernel-section covariance and feed it through the already-formalized cubic shell / uniform residual / physical sweep pipeline.
