# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative mixing, spatial influence, coercivity, and the mass-gap problem.

The repository is deliberately layered. Finite-volume probability statements, one-link laws, spatial influence estimates, covariance identities, weighted resolvents, coercivity interfaces, and continuum targets are kept separate so that a finite-volume theorem is never silently promoted into a continuum mass-gap theorem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current theorem development has now closed:
>
> - the fixed-volume complete-block/original-random-scan bridge and covariance-remainder limit;
> - an explicit fixed-volume restricted-random-scan resolvent route for the coarse tagged carrier;
> - the fixed-right finite-step and asymptotic response bounds under the explicit fixed-volume eligible-row criterion;
> - a volume-independent exponentially weighted Schur/resolvent theory for the genuine local Harnack carrier;
> - the exact decomposition of the full physical-left weighted column into the local contribution plus the actual source-aligned remote residual.
>
> The immediate open problem is now sharply isolated: prove a **non-circular exponentially weighted bound for the actual remote residual column**. That missing coefficient is not assumed or manufactured in the current formalization.

---

## Repository authority — theorem baseline 2026-09-20 JST

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this documentation refresh is:

    2fba0b625f39e581881bee1c2979b44c462bc62a

This is the merge commit of PR #4561:

    Isolate exponential weighted remote envelope column

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
      -> exact P_block^n = P_scan^(n * L_H) bridge
      -> Cov(F, P_scan^(n * L_H) G) -> 0
                                                        [INTEGRATED #4547-#4548]

    COARSE TAGGED RANDOM-SCAN RESOLVENT
      -> eligible-coordinate pullback
      -> geometric eligible-total contraction
      -> auxiliary unscanned response
      -> explicit eligible row coefficient
      -> fixed-right finite-step response resolvent
      -> asymptotic n-independent fixed-right bound
                                                        [INTEGRATED #4551-#4557]

    ACTUAL PHYSICAL LOCAL / REMOTE SPLIT
      -> actual local Harnack kernel
      -> local base-L1 propagation
      -> exact local + remote perturbation algebra
      -> source-aligned remote residual
      -> asymptotic fixed-right bridge retaining C5 remote support
                                                        [INTEGRATED through #4558]

    EXPONENTIAL WEIGHTED LOCAL HARNACK THEORY
      -> W_center(x) = s^baseL1Distance(center,x)
      -> local weighted row/column <= rho_s * W
      -> rho_s = 18 * eta(beta) * s^2
      -> K_local^d W <= rho_s^d W
      -> G_local,M W <= (1-rho_s)^(-1) W when rho_s < 1
                                                        [INTEGRATED #4559-#4560]

    FULL PHYSICAL WEIGHTED ENVELOPE
      -> exact weighted-column decomposition
           C_full = K_local + R_remote
      -> local weighted column <= rho_s * W(source)
      -> remote weighted column isolated exactly
      -> if R_remote,weighted <= kappa_s * W(source),
         then C_full weighted column
         <= (rho_s + kappa_s) * W(source)
                                                        [INTEGRATED #4561]

    CURRENT FRONTIER
      derive, rather than assume,

        R_remote,weighted(center,source)
          <= kappa_s * W_center(source)

      with a concrete volume-independent kappa_s and

        rho_s + kappa_s < 1

      from the actual physical / fixed-target law-level response machinery,
      without using terminal covariance decay, a physical contraction,
      Poincare/coercivity, or a mass gap upstream.
                                                        [OPEN NOW]

    DOWNSTREAM
      strict weighted physical influence control
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

# 1. Covariance remainder: closed at fixed finite volume

The older covariance telescope contains a remainder of the form

    Cov_mu(F, P_scan^M G).

The fixed-volume Doeblin route first proved complete-block convergence to the exact stationary reference mean. PR #4547 then identified the complete-block observable iterate with the original restricted-random-scan iterate at complete-block times:

    P_block^n f
      = P_scan^(n * L_H) f.

PR #4548 uses that identity to prove

    Cov_mu(F, P_scan^(n * L_H) G) -> 0

under the corresponding fixed-volume boundedness / oscillation hypotheses.

Therefore the covariance-remainder problem that was open in the previous README is no longer the current frontier.

This remains a fixed-volume ergodic statement. It does not supply a volume-uniform mixing constant or spatial correlation length.

---

# 2. Coarse tagged resolvent: useful but not the uniform spatial mechanism

PRs #4551-#4557 build an explicit restricted-random-scan resolvent for the tagged carrier.

The eligible-coordinate pullback admits geometric contraction under an explicit strict row criterion. In the physical specialization, PR #4553 computes the row sum exactly as

    (card(Link) - 1) * DistinctFiberOffFiberInfluence(beta).

This is an important structural result: the coarse left-left carrier is genuinely all-to-all at this level, so its contraction criterion is fixed-volume and deteriorates with the number of spatial links.

The subsequent auxiliary-coordinate and represented-right-source estimates yield a fixed-right finite-step response bound. PR #4557 sends the remaining geometric scan-depth term to zero, producing an n-independent **fixed-volume** asymptotic fixed-right bound.

These theorems are valid and reusable, but they do not by themselves solve volume-uniform spatial decay.

---

# 3. Actual physical remote bridge: scan depth removed

PR #4558 transports the asymptotic fixed-right response back to the actual source-aligned remote physical residual and through the local Green comparison.

The exact C5 remote support is retained rather than replaced by a global constant profile.

This removes the auxiliary random-scan depth from the physical-left remote bridge. However, the resulting amplitude is still controlled through the fixed-volume coarse eligible-row criterion. It is therefore not yet the desired volume-independent exponentially decaying spatial coefficient.

---

# 4. Exponentially weighted genuine local carrier: closed

The correct local spatial mechanism uses the genuine physical local Harnack kernel, not the dense tagged carrier.

Define the growing weight

    W_center(x)
      := s ^ baseL1Distance(center,x),

with

    s >= 1.

Because a nonzero local Harnack step changes base-L1 distance by at most two, PR #4559 proves the weighted Schur estimate

    sum_source
      K_local(target,source) * W_center(source)
      <=
      rho_s * W_center(target),

where

    rho_s
      := 18 * eta(beta) * s^2.

By symmetry, the corresponding weighted column estimate also holds.

PR #4560 iterates this inequality:

    K_local^d W
      <= rho_s^d W,

and, whenever

    rho_s < 1,

proves the uniform-in-depth finite local resolvent estimate

    G_local,M W
      <= (1 - rho_s)^(-1) * W.

This is volume-independent and preserves the exponential spatial weight throughout the iteration.

---

# 5. Full physical weighted envelope: exact frontier isolation

Let

    C_full(target,source)

denote the full physical-left influence envelope.

PR #4561 proves the exact exponentially weighted column decomposition

    sum_target
      C_full(target,source) * W_center(target)

      =

    sum_target
      K_local(target,source) * W_center(target)

      +

    R_remote,weighted(center,source).

The local term is bounded by

    rho_s * W_center(source).

The actual source-aligned remote term is left explicit:

    R_remote,weighted(center,source)
      :=
    sum_target
      R_remote(source,target) * W_center(target).

No remote coefficient is inserted by assumption.

The theorem also records the exact absorption interface: if one later proves

    R_remote,weighted(center,source)
      <= kappa_s * W_center(source),

then

    full weighted column
      <= (rho_s + kappa_s) * W_center(source).

If additionally

    rho_s + kappa_s < 1,

the full physical influence envelope becomes strictly subinvariant in the exponential weight.

That is the present theorem frontier.

---

# 6. Current open theorem: derive the remote weighted coefficient

The immediate target is a theorem that derives a concrete, volume-independent `kappa_s` for the **actual** remote residual.

The preferred route must preserve the real physical envelope / fixed-target law structure. A schematic target is

    R_remote,weighted(center,source)
      <= kappa_s(beta,s) * W_center(source),

with

    kappa_s(beta,s) >= 0

and a nonempty parameter regime satisfying

    18 * eta(beta) * s^2 + kappa_s(beta,s) < 1.

A self-consistent weighted response or bootstrap inequality is a natural candidate:

    actual response
      <= local direct term
        + local Green * remote forcing(actual response),

followed by weighted absorption.

What is not acceptable as closure:

    * assuming the desired remote weighted bound as a final hypothesis;
    * replacing the actual remote profile by the old all-to-all tagged carrier;
    * using terminal covariance decay to prove the weighted estimate that is itself needed upstream of that decay;
    * importing physical contraction, Poincare/coercivity, or mass-gap information as an assumption.

---

# 7. Downstream route after the weighted remote closure

Once a concrete strict weighted coefficient for the full physical influence envelope is proved, the intended route is

    exponentially weighted physical influence control
      -> spatial response / terminal kernel-section decay
      -> base-L1 exponential covariance decay
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

# 8. Permanent semantic boundaries

These distinctions are part of the proof discipline:

    finite-volume theorem != continuum theorem
    fixed-volume Doeblin rate != volume-uniform physical contraction
    random-scan ergodicity != spatial covariance decay
    covariance identity != covariance decay
    covariance decay != mass gap
    one-link conditional expectation != full Gibbs-law identification
    coarse tagged carrier != actual sparse physical carrier
    local Harnack propagation != remote residual control
    fixed-right asymptotic bound != volume-uniform spatial decay
    weighted local resolvent != weighted remote closure
    abstract absorption interface != proof of the absorption coefficient
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

No `sorry`, `admit`, new axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean `v4.30.0-rc2` with the repository-pinned mathlib revision. Repository lockfiles and the exact current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Closed through #4561:** exact finite-volume covariance-remainder closure on complete-block times; restricted-random-scan pullback resolvent; explicit physical eligible-row coefficient; auxiliary unscanned response; represented fixed-right source resolvent; finite-step and asymptotic fixed-right response bounds; asymptotic bridge back to the actual source-aligned remote residual; exponentially weighted local Harnack row/column control; iterated weighted local resolvent; exact full physical weighted-column decomposition; and the formal absorption gate for a future actual remote coefficient.

**Open now:** derive a concrete non-circular volume-independent bound for the actual exponentially weighted remote residual column, strong enough to make the full physical weighted coefficient strictly less than one. Then carry that strict spatial control into terminal covariance decay, the uniform remote-residual pipeline, coercivity, the uniform spectral gap, and finally the thermodynamic/continuum Yang--Mills construction.
