# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Exact finite-volume statements, continuous one-link probability laws, ground-state kernel-section laws, local and remote influence bounds, covariance identities, spatial propagation estimates, and continuum/OS targets are kept separate so that a finite-volume or conditional theorem is never silently promoted into a continuum mass-gap theorem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current continuous-`SU(N)` frontier has moved past a purely global finite-resolvent estimate. The repository now contains:
>
> - an exact source-singleton finite-resolvent reduction for the terminal kernel-section covariance;
> - a formal obstruction showing that the old coarse distinct-fiber carrier is spatially flat off the target;
> - a plaquette-local to base-`L1` separation bridge;
> - a singleton geometric finite-resolvent theorem in the sparse Dobrushin proxy lane;
> - an actual physical local Harnack influence kernel, separated exactly from the remote residual;
> - a fixed-target physical influence envelope for the exact kernel-section law;
> - and base-`L1` propagation/vanishing theorems for powers of the actual local Harnack kernel.
>
> The remaining central task is therefore **not** to sharpen the old dense carrier. It is to combine the now-formalized local spatial Green/resolvent structure with the exact remote residual and the finite covariance remainder, without circularly assuming the very covariance decay needed to control that residual.

---

## Repository authority — documentation baseline 2026-09-19 JST

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing commit used for this documentation refresh is:

    550a84c972ac3c289d1b70ba7ec9c2beab0b3501

This is the merge commit of PR #4521:

    Propagate physical local Harnack influence in base-L1

This README/ROADMAP refresh is documentation-only. After the docs PR merges, the branch pointer will advance while the theorem-bearing mathematical baseline remains PR #4521 until a later theorem PR lands. Always fresh-fetch the theorem-carrier branch before theorem work.

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

    ACTUAL REMOTE INFLUENCE + PHYSICAL ENVELOPE
      -> targetwise cross-ratio majorant
      -> actual remote bounded-test influence
      -> source-aligned remote residual
      -> active Harnack + remote physical envelope
      -> finite-volume strict-gate contraction
                                                        [INTEGRATED #4464-#4478]

    UNIFORM REMOTE-RESIDUAL REDUCTION
      -> two-step terminal normal form
      -> crossing denominator floor
      -> cubic base-L1 shell bound
      -> terminal covariance decay => uniform residual rho
                                                        [INTEGRATED #4479-#4494]

    EXACT KERNEL-SECTION COVARIANCE MECHANICS
      -> remote one-link conditional expectation
      -> L2 projection / fluctuation identities
      -> one-link covariance Dirichlet identity
      -> deterministic schedule telescope
      -> restricted-random-scan finite resolvent
                                                        [INTEGRATED #4495-#4513]

    SPATIAL RESOLVENT REFINEMENT
      -> source crossing variation is exactly singleton-supported
      -> terminal finite-resolvent sum collapses to one source entry
      -> coarse distinct-fiber carrier proven spatially flat off target
                                                        [INTEGRATED #4515-#4516]

    PLAQUETTE-LOCAL / BASE-L1 GEOMETRY
      -> one plaquette-local step changes link-base L1 by <= 2
      -> length-d local path has base-L1 distance <= 2d
      -> base-L1 distance >= 2D implies local path separation D
                                                        [INTEGRATED #4518]

    SPARSE PROXY GREEN BOUND
      -> singleton forcing
      -> base-L1 separated finite resolvent
      -> geometric bound under a strict sparse Dobrushin proxy gate
                                                        [INTEGRATED #4519]
                                                        [PROXY ONLY]

    ACTUAL PHYSICAL LOCAL HARNACK KERNEL
      -> exact local kernel supported on active neighbors
      -> nonzero local influence => shared Wilson plaquette
      -> physical envelope = local Harnack + remote residual
      -> local row/column mass <= 18 * eta_local(beta)
                                                        [INTEGRATED #4520-#4521]

    ACTUAL LOCAL BASE-L1 PROPAGATION
      -> local Harnack kernel powers
      -> degree-d row mass <= (18 * eta_local(beta))^d
      -> nonzero degree-d coefficient => base-L1 distance <= 2d
      -> distance >= 2D => all degrees d < D vanish exactly
                                                        [INTEGRATED #4521]

    CURRENT ANALYTIC FRONTIER
      -> sum the actual local Harnack powers into a geometric local resolvent
      -> insert the exact remote residual as a perturbation
      -> control the finite random-scan covariance remainder
      -> obtain non-circular terminal kernel-section covariance decay
      -> feed cubic shell theorem to get uniform remote residual rho
                                                        [OPEN NOW]

    DOWNSTREAM
      uniform physical sweep contraction
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic/scaling-limit physical carrier
      -> sufficiently rich 4D Yang--Mills field/state
      -> Clay-level existence + mass gap
                                                        [OPEN]

---

# 1. The old dense carrier is now a proved obstruction, not a candidate final route

PR #4516 formalizes a key negative result about the existing coarse distinct-fiber restricted-scan carrier.

Starting from a singleton fixed-right target variation, the one-step coarse profile is spatially flat across all off-target sources. In particular, two off-target sources at different base-`L1` radii receive the same value.

This is a statement about the **coarse carrier**, not about the exact physical covariance. Its role is architectural: it proves that no amount of algebraic sharpening of the same distance-blind coefficient can produce the required spatial decay.

Therefore the intended route is now fixed:

    local spatial kernel / Green propagation
      + genuinely remote physical residual
      + exact covariance telescope,

rather than:

    dense off-fiber coefficient
      -> global contraction
      -> hoped-for spatial decay.

---

# 2. The terminal finite-resolvent estimate is spatially localized at the source

PR #4515 refines the #4513 covariance-resolvent telescope.

The source crossing-ratio observable has an exact physical-left variation profile supported on a single source fiber:

    variation_source(e)
      = exp(2*beta) - exp(-2*beta)   if e = source
      = 0                            otherwise.

The actual two-step terminal target observable has an explicit propagated variation profile.

Because the source profile is singleton-supported, the generic finite-resolvent pairing collapses from a sum over all fibers to a single source entry of the terminal finite resolvent.

This is a genuine spatial refinement, but it is still finite-volume and finite-`M`. It does **not** remove the covariance remainder and does **not** by itself prove exponential decay.

---

# 3. Plaquette locality is now connected rigorously to base-L1 distance

PR #4518 supplies the geometry needed to convert sparse propagation depth into the canonical spatial distance used by the terminal shell theorems.

One actual Wilson-plaquette-local step changes periodic link-base `L1` distance by at most two:

    localStep(target, source)
      -> baseL1Distance(target, source) <= 2.

Hence a plaquette-local path of length `d` satisfies:

    baseL1Distance(target, source) <= 2*d.

Conversely, if:

    2*D <= baseL1Distance(target, source),

then singleton supports at target and source are separated by at least `D` plaquette-local propagation steps.

This is the bridge that lets a genuinely sparse local influence kernel produce base-`L1` spatial decay.

---

# 4. A sparse singleton resolvent theorem exists, but it is a proxy theorem

PR #4519 proves a geometric finite-resolvent estimate for singleton forcing in the sparse Dobrushin proxy lane.

Under its own strict proxy hypothesis, base-`L1` separation forces a geometric tail of the form

    const * q^D / (1 - q)

after converting distance to a minimum propagation depth.

This theorem is useful because it formalizes the algebra and geometry of the desired Green-function mechanism.

However:

> **The #4519 kernel is not identified with the actual continuous-vacuum physical kernel-section law.**

In particular, its coefficient must not be silently equated with the physical Harnack coefficient introduced below. The theorem is a reusable proxy/model lemma, not the final physical decay theorem.

---

# 5. The actual physical local Harnack kernel is now explicit

PR #4520 extracts the genuinely local part of the actual physical left influence envelope.

Define a local influence kernel that is:

    eta_local(beta)   on intrinsic active neighbors,
    0                 elsewhere,

where `eta_local(beta)` is the already-formalized background-update Harnack influence coefficient.

The repository proves:

    local influence = 0 off the active-neighbor graph,

    nonzero local influence
      -> intrinsic active-neighbor relation
      -> shared spatial Wilson plaquette,

and, crucially, the exact decomposition:

    PhysicalLeftInfluenceEnvelope
      = LocalHarnackKernel
      + SourceAlignedRemotePhysicalResidual.

Every source column of the local kernel is bounded by:

    18 * eta_local(beta).

The actual bounded-test one-link response is controlled by the same local kernel plus the unchanged remote residual.

This is the physical sparse/remote decomposition needed after the dense-carrier obstruction.

---

# 6. The exact fixed-target kernel-section law also has a sparse/remote envelope

PR #4517 builds a fixed-target physical left-left influence envelope for the exact kernel-section one-link law used by the terminal covariance.

For an off-diagonal target/source pair:

    C5-exceptional pair
      -> background-update Harnack coefficient,

    C5-remote pair
      -> target-specific actual remote cross-ratio residual.

The law-level bounded-test response is dominated by this fixed-target envelope.

This distinction matters:

    source-aligned envelope
      != fixed-target kernel-section envelope.

The repository now has both interfaces, and they must remain separate unless an explicit theorem connects them.

---

# 7. Powers of the actual local Harnack kernel now propagate in base-L1

PR #4521 is the current theorem-bearing frontier.

The physical local Harnack kernel is symmetric, so row and column sums agree. Every row is bounded by:

    rho_local(beta) := 18 * eta_local(beta).

Recursive powers of the actual local kernel are formalized. For degree `d`:

    rowMass(K_local^d)
      <= rho_local(beta)^d.

More importantly, spatial support is exact:

    K_local^d(target, source) != 0
      -> baseL1Distance(target, source) <= 2*d.

Therefore, if:

    2*D <= baseL1Distance(target, source),

then for every `d < D`:

    K_local^d(target, source) = 0.

This is the first actual physical local-kernel theorem in the repository that simultaneously carries:

    volume-independent mass control
    + finite propagation speed
    + canonical base-L1 spatial information.

---

# 8. What remains open now

The next theorem layer should sum the actual local powers into a finite/infinite geometric local resolvent under:

    rho_local(beta) < 1.

Because all degrees below the spatial separation threshold vanish exactly, the local Green tail should have the schematic form:

    G_local(target, source)
      <= rho_local(beta)^D / (1 - rho_local(beta))

whenever the base-`L1` distance is at least `2D`.

That local result alone is still insufficient. The exact physical law contains the remote term:

    K_physical = K_local + R_remote.

The next nontrivial step is therefore a local-plus-remote perturbation theorem that preserves distance information. Schematically, one needs to reorganize a response/subinvariant inequality such as

    w <= v + K_local^T w + R_remote^T w

through the local Green operator, without assuming the final covariance decay in order to bound `R_remote`.

The second unresolved issue is the finite random-scan remainder:

    Cov(F, P_scan^M G).

The #4513/#4515 finite-resolvent theorem controls only the first `M` covariance decrements. It does not prove that this remainder vanishes as `M -> infinity`.

Thus the current central analytic problem has two coupled parts:

    1. local spatial Green decay + remote perturbation control;
    2. a justified treatment of the covariance remainder.

Only after those are closed can the #4493 terminal covariance-decay predicate be established non-circularly.

---

# 9. Existing uniform-residual pipeline remains ready downstream

The earlier #4479-#4494 route is unchanged and remains available once terminal covariance decay is proved.

The exact terminal response is bounded by:

    exp(2*beta) * |kernelSectionCovariance|,

because the crossing expectation denominator obeys the volume-independent floor:

    crossingExpectation >= exp(-2*beta).

The source-aligned remote base-`L1` shell satisfies:

    shellCard(r) <= 3 * (2*r + 1)^3,

and the cubic shell majorant times `q^r` is summable for every:

    0 <= q < 1.

Therefore an eventual volume-uniform exponential terminal covariance bound feeds directly into:

    terminal covariance decay
      -> terminal response decay
      -> uniform shell mass
      -> explicit remote residual rho
      -> strict physical sweep gate.

No artificial shell-growth condition such as `18*q < 1` is needed for this downstream cubic-shell summation.

---

# 10. Permanent semantic boundaries

These distinctions are part of the proof discipline:

    finite-volume theorem != continuum theorem
    one-link conditional expectation != full Gibbs-law identification
    covariance identity != covariance decay
    covariance decay != mass gap
    variation propagation != correlation decay automatically
    graph-distance shell != base-L1 shell
    fixed-right response != actual physical influence
    source-aligned envelope != fixed-target envelope
    sparse proxy kernel != actual physical local Harnack kernel
    local Harnack propagation != control of the remote residual
    finite resolvent != infinite resolvent / vanishing remainder
    strict finite-volume gate != uniform-in-volume gate
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap

No `sorry`, `admit`, new axioms, hidden constants, weakened hypotheses, or theorem weakening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean `v4.30.0-rc2` with the repository-pinned mathlib revision. The exact repository lockfiles and current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Closed:** actual remote conditional influence; physical local/remote envelope; terminal covariance normal form and denominator floor; cubic base-`L1` shell geometry; exact kernel-section conditional expectation and `L2` projection identities; deterministic/restricted-random-scan covariance telescopes; source-singleton finite-resolvent reduction; formal dense-carrier spatial-flatness obstruction; plaquette-local/base-`L1` separation; sparse proxy singleton Green estimate; actual local Harnack kernel; fixed-target physical envelope; and actual local-Harnack base-`L1` propagation.

**Open now:** sum the actual local Harnack powers into a distance-sensitive geometric resolvent, combine that local Green operator with the exact remote residual without circularity, control the finite covariance remainder, and thereby prove volume-uniform base-`L1` decay of the exact terminal kernel-section covariance.
