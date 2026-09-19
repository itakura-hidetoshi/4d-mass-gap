# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Finite-volume probability statements, continuous one-link laws, spatial influence estimates, covariance identities, mixing arguments, coercivity interfaces, and continuum targets are kept separate so that a local or finite-volume theorem is never silently promoted into a continuum mass-gap theorem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current continuous-`SU(N)` development has now closed two substantial finite-volume subroutes:
>
> 1. a spatial local-Green route through a base-`L1` weighted remote convolution and an explicit bridge to a fixed-right finite-step response;
> 2. an independent restricted-random-scan Doeblin route through a common Haar minorization, coupling, geometric `rho^n` contraction, vanishing residual factor, and explicit convergence of complete-block iterates to the stationary reference expectation.
>
> The immediate open work is now narrower: identify the complete-block iterate exactly with the original restricted-random-scan iterate at times `M = n * L_H` and use that bridge to close the covariance remainder, while separately proving a non-circular spatial estimate for the fixed-right weighted remote response.

---

## Repository authority — theorem baseline 2026-09-20 JST

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this documentation refresh is:

    172973dac7222ff66f8332580888916dfa202a82

This is the merge commit of PR #4545:

    Identify the Doeblin block limit with the stationary reference mean

This README/ROADMAP refresh is documentation-only. After the docs PR merges, the branch pointer may advance while the mathematical theorem baseline remains the most recent theorem-bearing merge unless another theorem PR lands first.

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
      -> one-slab transfer and ground-state structure
      -> coercivity / spectral routing
                                                        [INTEGRATED]

    CONTINUOUS ONE-LINK LAW + LOCAL GEOMETRY
      -> normalized continuous SU(N) fiber law
      -> measurable heat-bath reinsertion
      -> stationarity / represented-source cancellation
      -> active-neighbor degree <= 18
      -> C5 exceptional set <= 20
                                                        [INTEGRATED]

    EXACT KERNEL-SECTION / COVARIANCE MECHANICS
      -> one-link conditional expectation
      -> L2 projection / fluctuation identities
      -> deterministic and restricted-random-scan telescopes
      -> finite covariance resolvent
                                                        [INTEGRATED #4495-#4513]

    SOURCE LOCALIZATION + SPATIAL OBSTRUCTION
      -> terminal source variation is singleton-supported
      -> coarse distinct-fiber carrier is spatially flat off target
      -> local propagation must be separated from remote forcing
                                                        [INTEGRATED #4515-#4516]

    ACTUAL LOCAL HARNACK / BASE-L1 GREEN ROUTE
      -> plaquette-local step changes base-L1 distance by <= 2
      -> actual local Harnack kernel
      -> exact finite propagation of kernel powers
      -> finite Green tail <= rho_local^D/(1-rho_local)
      -> exact local + remote perturbation algebra
      -> singleton forcing inherits local geometric decay
                                                        [INTEGRATED #4518-#4525]

    WEIGHTED REMOTE ROUTE
      -> coarse remote column-mass reduction
      -> base-L1 weighted local Green convolution
      -> weighted remote column W_remote(target,source)
      -> W_remote bounded by a configuration-independent
         fixed-right finite-step weighted response profile
                                                        [INTEGRATED #4526-#4529]

    INDEPENDENT FIXED-VOLUME DOEBLIN ROUTE
      -> every reference one-link law minorizes Haar
      -> heat-bath kernel inherits the Haar minorization
      -> finite deterministic schedules are Markov kernels
      -> schedule minorization composes
      -> complete Haar refresh sweep forgets the initial state
                                                        [INTEGRATED #4530-#4536]

    ACTUAL RESTRICTED RANDOM SCAN
      -> actual restricted random scan is a Markov kernel
      -> reference probability law is stationary
      -> complete block dominates a common Haar-refresh law
      -> Doeblin coefficient delta > 0
      -> residual mass rho = 1-delta satisfies rho < 1
      -> exact two-row Doeblin coupling
                                                        [INTEGRATED #4537-#4540]

    OBSERVABLE CONTRACTION AND FIXED-VOLUME ERGODIC LIMIT
      -> one complete block contracts pairwise oscillation by rho
      -> n complete blocks contract by rho^n
      -> rho.toReal < 1 and rho.toReal^n -> 0
      -> every complete-block iterate preserves the exact reference mean
      -> |P_block^n f(A) - E_mu[f]| <= rho.toReal^n * R
      -> P_block^n f(A) -> E_mu[f] at every fixed finite volume
                                                        [INTEGRATED #4541-#4545]

    CURRENT FRONTIER
      ERGODIC / COVARIANCE SIDE:
        prove the exact bridge
          P_block^n f = P_scan^(n * L_H) f
        for the original restricted-random-scan observable iterate
        -> close Cov(F, P_scan^(n * L_H) G) -> 0

      SPATIAL SIDE:
        prove a non-circular base-L1 decay / weighted operator estimate
        for the fixed-right finite-step weighted remote profile

      COMBINE:
        local Green + weighted remote control
        + covariance-remainder closure
        -> exact terminal kernel-section base-L1 covariance decay
                                                        [OPEN NOW]

    DOWNSTREAM
      terminal covariance decay
      -> cubic shell summability
      -> uniform remote residual
      -> strict physical sweep gate
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic / continuum physical carrier
      -> sufficiently rich 4D Yang--Mills field/state
      -> Clay-level existence + mass gap
                                                        [OPEN]

---

# 1. Local spatial mechanism: closed through the weighted fixed-right bridge

The old coarse distinct-fiber carrier cannot provide spatial decay: PR #4516 proves that its one-step off-target profile is spatially flat. The current spatial mechanism instead uses the actual local Harnack kernel.

Let

    K_local(target, source)

be the intrinsic active-neighbor Harnack kernel and define schematically

    rho_local(beta) := 18 * eta_local(beta).

The repository proves:

    rowMass(K_local^d) <= rho_local(beta)^d,

and

    K_local^d(target,source) != 0
      -> baseL1Distance(target,source) <= 2*d.

Hence a base-`L1` separation of at least `2D` kills every local degree below `D`. Under `rho_local < 1`, the finite local Green kernel obeys

    R_local,M(target,source)
      <= rho_local^D / (1-rho_local).

The exact physical comparison is reorganized without assuming remote smallness:

    w <= v + (K_local + R_remote)w

becomes

    w
      <= G_local,M v
        + G_local,M(R_remote w)
        + K_local^M w.

For singleton source forcing, the direct term inherits the base-`L1` geometric Green decay.

---

# 2. Weighted remote convolution: geometry is preserved

PR #4527 replaces the coarse global-`L1` collapse by a spatially resolved weight.

Define

    depth(target,mid)
      := floor(baseL1Distance(target,mid) / 2),

and

    G_weight(target,mid)
      := rho_local^depth(target,mid) / (1-rho_local).

Then the exact remote forcing is propagated through

    W_remote(target,source)
      :=
    sum_mid
      G_weight(target,mid)
      * R_remote(source,mid).

The singleton comparison has schematic form

    w(target)
      <=
    rho_local^D/(1-rho_local) * amplitude
      +
    sum_source W_remote(target,source) * w(source)
      +
    rho_local^M * distanceBound.

PR #4529 then proves that every source-aligned physical remote residual is bounded by an existing fixed-right finite-step target-response bound, and lifts that comparison through the local Green convolution.

Therefore the weighted remote term is no longer tied to an arbitrary background configuration: it is controlled by a configuration-independent fixed-right finite-step weighted response profile.

What is **not** yet proved is the required non-circular spatial decay or weighted absorption estimate for that fixed-right profile.

---

# 3. Independent Doeblin route for the covariance remainder

The covariance telescope from #4513 has the schematic form

    Cov(F,G)
      = finite covariance decrement
        + Cov(F, P_scan^M G).

The second term cannot be discarded merely because the finite resolvent is controlled.

To close it independently of terminal covariance decay, PRs #4530-#4545 build a fixed-volume Doeblin/ergodic route.

## 3.1 One-link Haar minorization

PR #4530 proves a strictly positive Haar minorization for every reference one-link law. PR #4531 lifts it to the actual heat-bath kernel.

PRs #4532-#4534 package deterministic schedules as kernels and propagate the one-link minorization through finite schedules.

PR #4536 proves that a complete Haar-refresh sweep forgets its initial configuration exactly, while the actual deterministic complete sweep dominates the same initial-state-independent Haar-refresh law.

The coefficient may deteriorate with volume. That is acceptable here: this route is used only for fixed-volume ergodicity and covariance-remainder closure, not as a volume-uniform physical contraction constant.

## 3.2 Actual restricted random scan and full-block Doeblin minorization

PR #4537 packages the actual restricted random scan as a Markov kernel and proves exact stationarity of the normalized continuous-vacuum reference law.

PR #4538 proves that a prescribed complete deterministic schedule appears inside a complete-length random-scan block with the exact product of uniform selection coefficients. Combining this with the deterministic Haar minorization gives a common full-block lower bound

    delta * nu_Haar <= P_block(A, ·)

for every initial configuration `A`, with `delta > 0` at every fixed finite volume.

PR #4539 splits each block row exactly into

    P_block(A, ·)
      = delta * nu_Haar + residual_A,

with

    residual_A(univ) = rho := 1 - delta

and

    rho < 1.

## 3.3 Coupling and geometric observable contraction

PR #4540 constructs an exact coupling of any two complete-block rows. The common Haar mass is coupled diagonally, and the probability of unequal endpoints is at most `rho`.

PR #4541 turns that coupling into the sharp one-block oscillation estimate

    |P_block f(A) - P_block f(C)|
      <= rho.toReal * R

whenever

    |f(X) - f(Y)| <= R

for all `X,Y`.

PR #4542 iterates the estimate:

    |P_block^n f(A) - P_block^n f(C)|
      <= rho.toReal^n * R.

PR #4543 proves

    rho.toReal < 1

and

    rho.toReal^n -> 0.

PR #4545 then uses exact block stationarity and Fubini to prove that every complete-block iterate preserves the exact normalized reference mean, and sharpens the pairwise contraction to

    |P_block^n f(A) - E_mu[f]|
      <= rho.toReal^n * R.

Consequently, at every fixed finite volume,

    P_block^n f(A) -> E_mu[f]

for every initial configuration `A` under the stated strong-measurability and finite global oscillation hypotheses.

---

# 4. Immediate open theorem on the covariance-remainder side

The fixed-volume stationary-limit identification is now closed. The next task is to connect that block theory to the exact observable iterate already appearing in the #4513 covariance telescope.

Let

    L_H := length(allSpatialLinkSchedule H).

The required bridge is an exact theorem of the form

    P_block^n f
      = P_scan^(n * L_H) f,

with the repository's existing recursive conventions on kernel composition and observable iteration matched explicitly.

Once this bridge is formalized, #4545 gives the complete-block-time remainder limit

    Cov_mu(F, P_scan^(n * L_H) G) -> 0

for the relevant bounded/finite-oscillation observables. This is enough to close the covariance telescope along the complete-block subsequence, provided the exact step/block identification is proved.

This remains a fixed-volume closure. No volume-uniform Doeblin coefficient is required.

---

# 5. Immediate open theorem on the spatial side

The remaining spatial object is the configuration-independent fixed-right finite-step weighted response obtained in #4529.

A useful theorem would have one of the forms

    W_fixed(target,source)
      <= C_remote * q_remote^baseL1Distance(target,source),

with `0 <= q_remote < 1`, or a weighted Schur/subinvariant estimate strong enough to absorb the weighted remote forcing in an exponential spatial norm.

Critical non-circularity rule:

    terminal covariance decay
      -> uniform remote residual

is already a valid downstream implication.

But the same terminal covariance decay may not be assumed upstream to prove the weighted remote estimate that is needed to derive it.

---

# 6. Downstream route after the two current frontiers close

Once the spatial weighted-response estimate and covariance-remainder closure are both available, the intended route is

    source-singleton variation
      -> actual local Green decay
      -> weighted fixed-right remote control
      + fixed-volume random-scan covariance-remainder vanishing
      -> exact terminal kernel-section base-L1 covariance decay
      -> cubic shell summability
      -> volume-uniform remote residual
      -> strict physical sweep gate
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic / continuum physical limit
      -> sufficiently rich nontrivial 4D Yang--Mills state/field
      -> spectral mass gap above the vacuum.

Every arrow remains subject to its own Lean theorem and hypotheses.

---

# 7. Permanent semantic boundaries

These distinctions are part of the proof discipline:

    finite-volume theorem != continuum theorem
    one-link conditional expectation != full Gibbs-law identification
    covariance identity != covariance decay
    covariance decay != mass gap
    fixed-volume Doeblin rate != volume-uniform physical contraction
    random-scan mixing != spatial covariance decay
    source-aligned envelope != fixed-target kernel-section envelope
    local Harnack propagation != remote residual control
    finite local Green resolvent != covariance-remainder vanishing
    weighted remote bridge != weighted remote decay
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

No `sorry`, `admit`, new axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening are accepted as substitutes for proof.

PR #4535 was closed without merge and is not part of the canonical theorem history.

---

## Toolchain

The formalization currently tracks Lean `v4.30.0-rc2` with the repository-pinned mathlib revision. Repository lockfiles and the exact current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Closed through #4545:** exact kernel-section covariance mechanics; source-singleton localization; dense-carrier obstruction; actual local-Harnack finite propagation; actual local Green tail; exact local-plus-remote perturbation; base-`L1` weighted remote convolution; fixed-right finite-step bridge; one-link Haar minorization; deterministic full-sweep Haar refresh; actual restricted-random-scan Markov kernel and stationarity; complete-block Doeblin minorization; residual decomposition; exact coupling; geometric `rho^n` oscillation contraction; `rho.toReal^n -> 0`; exact preservation of the stationary reference mean by all complete-block iterates; the bound `|P_block^n f(A) - E_mu[f]| <= rho.toReal^n * R`; and pointwise convergence to the reference expectation at every fixed finite volume.

**Open now:** prove the exact complete-block/step-iterate bridge `P_block^n = P_scan^(n * L_H)` and use it to close the #4513 covariance remainder; independently prove spatial decay or weighted absorption for the fixed-right weighted remote profile; then combine the two to obtain exact terminal kernel-section base-`L1` covariance decay.
