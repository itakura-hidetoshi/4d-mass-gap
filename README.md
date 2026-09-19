# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, conditional expectation, quantitative mixing, coercivity, and the mass-gap problem.

The repository is deliberately layered. Exact finite-volume statements, continuous one-link probability laws, kernel-section conditional expectations, local and remote influence kernels, covariance identities, spatial propagation estimates, coercivity interfaces, and continuum/OS targets are kept separate so that a finite-volume or conditional theorem is never silently promoted into a continuum mass-gap theorem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current continuous-`SU(N)` frontier has advanced beyond merely identifying a local physical carrier. The repository now contains:
>
> - exact source-singleton localization of the terminal covariance resolvent;
> - a formal obstruction showing that the old coarse distinct-fiber carrier is spatially flat off target;
> - a rigorous plaquette-local to base-`L1` bridge;
> - the actual physical local Harnack kernel and its exact decomposition from the remote physical residual;
> - base-`L1` finite propagation for powers of that actual local kernel;
> - a geometric finite local resolvent bound under the strict local threshold;
> - an exact local-plus-remote perturbation identity with the remote term retained as forcing;
> - a singleton local Green estimate with explicit remote and finite-local remainders;
> - a reduction of the remote contribution first to source-column mass and then, more sharply, to a **base-`L1` weighted remote convolution**.
>
> The central analytic problem is now to control that weighted remote convolution **without** assuming the final terminal covariance decay, and to close the separate restricted-random-scan covariance remainder.

---

## Repository authority — theorem baseline 2026-09-19 JST

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact current theorem-bearing commit used for this documentation refresh is:

    7e07ea2d7579839f20d08559b39dcb397bf42ebc

This is the merge commit of PR #4527:

    Preserve base-L1 geometry in remote local-Green convolution

This README/ROADMAP refresh is documentation-only. After the docs PR merges, the branch pointer may advance, while the mathematical theorem baseline remains the most recent theorem-bearing merge unless another theorem PR lands first. Always fresh-fetch the theorem-carrier branch before theorem work.

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
                                                        [DOWNSTREAM INPUT STILL OPEN]

    EXACT KERNEL-SECTION COVARIANCE MECHANICS
      -> remote one-link conditional expectation
      -> L2 projection / fluctuation identities
      -> one-link covariance Dirichlet identity
      -> deterministic schedule telescope
      -> restricted-random-scan finite resolvent
                                                        [INTEGRATED #4495-#4513]

    SOURCE LOCALIZATION + DENSE-CARRIER OBSTRUCTION
      -> source crossing variation is singleton-supported
      -> finite-resolvent pairing collapses to one source entry
      -> old coarse distinct-fiber carrier is spatially flat off target
                                                        [INTEGRATED #4515-#4516]

    PLAQUETTE-LOCAL / BASE-L1 GEOMETRY
      -> one local step changes link-base L1 by <= 2
      -> length-d local path has base-L1 distance <= 2d
      -> distance >= 2D implies local path separation D
                                                        [INTEGRATED #4518]

    SPARSE PROXY GREEN BOUND
      -> singleton forcing
      -> separated finite-resolvent geometric tail
                                                        [INTEGRATED #4519]
                                                        [PROXY ONLY]

    ACTUAL PHYSICAL LOCAL HARNACK KERNEL
      -> exact active-neighbor local kernel
      -> physical envelope = local Harnack + remote residual
      -> row/column mass <= 18 * eta_local(beta)
      -> powers have exact base-L1 finite propagation
                                                        [INTEGRATED #4520-#4521]

    ACTUAL LOCAL GREEN / RESOLVENT
      -> exact finite local resolvent
      -> all degrees d < D vanish at distance >= 2D
      -> finite tail <= rho_local^D / (1-rho_local)
                                                        [INTEGRATED #4523]

    LOCAL + REMOTE PERTURBATION
      -> w <= v + (K_local + R_remote)w
      -> reorganized as local Green with explicit remote forcing
      -> no remote-smallness assumption used
      -> finite local power remainder retained explicitly
                                                        [INTEGRATED #4524]

    SINGLETON SOURCE THROUGH LOCAL GREEN
      -> generic powers/resolvents matched to actual local kernel entries
      -> direct singleton term gets base-L1 geometric decay
      -> remaining terms:
           G_local(R_remote w)
           + finite local remainder
                                                        [INTEGRATED #4525]

    REMOTE COLUMN-MASS REDUCTION
      -> local Green of nonnegative forcing <= inverse local gap * L1 mass
      -> remote forcing mass = weighted source-column pairing exactly
      -> optional column bound gives global-L1 estimate
                                                        [INTEGRATED #4526]
                                                        [COARSE FALLBACK]

    BASE-L1 WEIGHTED REMOTE CONVOLUTION
      -> arbitrary local resolvent decomposes sourcewise
      -> canonical depth = floor(baseL1Distance / 2)
      -> local Green weight retains target/intermediate geometry
      -> remote forcing propagated as:
           sum_source [
             sum_mid G_local_weight(target,mid) * R_remote(source,mid)
           ] * w(source)
                                                        [INTEGRATED #4527]
                                                        [CURRENT THEOREM FRONTIER]

    CURRENT ANALYTIC FRONTIER
      -> control the weighted remote column non-circularly
      -> connect the source-aligned perturbation route to the exact
         fixed-target kernel-section law where needed
      -> close the distinct restricted-random-scan covariance remainder
      -> obtain exact terminal kernel-section base-L1 covariance decay
                                                        [OPEN NOW]

    DOWNSTREAM
      terminal covariance decay
      -> cubic shell summability
      -> uniform remote residual rho
      -> strict physical sweep gate
      -> physical Poincare / coercivity
      -> uniform finite-volume transfer/Hamiltonian gap
      -> thermodynamic/continuum physical carrier
      -> sufficiently rich 4D Yang--Mills field/state
      -> Clay-level existence + mass gap
                                                        [OPEN]

---

# 1. The old dense carrier is an obstruction, not the final spatial mechanism

PR #4516 formalizes a negative result about the old coarse distinct-fiber restricted-scan carrier.

Starting from a singleton fixed-right target variation, the one-step coarse profile is spatially flat across off-target sources. Different off-target sources at different base-`L1` radii can receive the same value.

This is a statement about the **carrier**, not about the exact physical covariance. Its architectural consequence is permanent:

    do not try to extract spatial decay
    by repeatedly sharpening the same distance-blind dense coefficient.

The final route must keep local finite propagation and the genuinely remote physical residual separate.

---

# 2. Source localization and the covariance telescope

PR #4515 refines the #4513 covariance-resolvent telescope.

The source crossing-ratio observable has an exact physical-left variation profile supported on one source fiber:

    variation_source(e)
      = exp(2*beta) - exp(-2*beta)   if e = source
      = 0                            otherwise.

Therefore the generic finite-resolvent pairing collapses to one source coordinate.

The covariance telescope still has the form

    Cov(F,G)
      = finite covariance decrement contribution
        + Cov(F, P_scan^M G),

schematically. The first term is now highly localized. The second term is a **separate covariance remainder** and remains open.

Permanent boundary:

    finite resolvent
      != vanishing covariance remainder
      != ergodicity.

---

# 3. The physical local kernel now has exact base-L1 finite propagation

PRs #4520-#4521 isolate the genuinely local part of the actual physical influence envelope:

    K_local(target, source)
      = eta_local(beta)   on intrinsic active neighbors
      = 0                 otherwise.

The repository proves the exact decomposition

    PhysicalLeftInfluenceEnvelope
      = K_local + R_remote,

where `R_remote` is the source-aligned remote physical residual.

Define

    rho_local(beta) := 18 * eta_local(beta).

The local kernel is symmetric; its row and column masses are bounded by `rho_local(beta)`. Recursive powers satisfy

    rowMass(K_local^d) <= rho_local(beta)^d,

and, crucially,

    K_local^d(target, source) != 0
      -> baseL1Distance(target, source) <= 2*d.

Hence

    2*D <= baseL1Distance(target, source)

implies

    K_local^d(target, source) = 0

for every `d < D`.

This is actual physical local-kernel propagation, not the older sparse proxy theorem.

---

# 4. The actual local Green tail is now formalized

PR #4523 sums the powers of the actual local Harnack kernel into a finite local resolvent.

For every finite truncation `M`, base-`L1` separation removes the complete low-degree prefix exactly. Under

    rho_local(beta) < 1,

the finite resolvent entry satisfies

    R_local,M(target, source)
      <= rho_local(beta)^D / (1 - rho_local(beta))

whenever

    2*D <= baseL1Distance(target, source).

The bound is uniform in `M`.

This closes the previously open “sum the actual local powers” step.

Boundary:

    local Green decay
      != control of the full physical law,

because the exact physical envelope still contains `R_remote`.

---

# 5. The full physical comparison is reorganized through the local Green operator

PR #4524 formalizes the perturbative algebra.

A comparison inequality of the form

    w <= v + (K_local + R_remote) w

is reorganized exactly as

    w <= (v + R_remote w) + K_local w.

Only `K_local` is iterated. The remote contribution remains explicit forcing.

For finite truncation `M` one obtains schematically

    w
      <= G_local,M v
        + G_local,M(R_remote w)
        + K_local^M w.

Using the local row-mass bound, the final local remainder is bounded by

    rho_local(beta)^M * distanceBound.

No remote smallness is used in this step, and no terminal covariance-decay assumption is imported.

---

# 6. Singleton forcing now receives the actual physical local Green decay

PR #4525 identifies the generic finite kernel powers and partial resolvent with the recursive local-Harnack kernel entries.

For singleton forcing of amplitude `a` at `source`, the direct local contribution therefore obeys

    G_local,M(singleton_source * a)(target)
      <= rho_local(beta)^D / (1-rho_local(beta)) * a

at base-`L1` separation at least `2D`.

Combining this with #4524 gives

    w(target)
      <= rho_local^D/(1-rho_local) * a
        + G_local,M(R_remote w)(target)
        + rho_local^M * distanceBound.

This is the first theorem in the current route that simultaneously carries:

    actual physical local coefficient
    + source-singleton localization
    + base-L1 geometric decay
    + explicit remote perturbation
    + explicit finite local remainder.

---

# 7. The remote perturbation can be reduced to column mass, but that is intentionally not the final route

PR #4526 proves a useful coarse reduction.

For nonnegative forcing `b`,

    G_local,M b(target)
      <= 1/(1-rho_local) * sum_source b(source).

For the physical remote forcing, its total mass is identified exactly as

    sum_target (R_remote w)(target)
      =
    sum_source [
      remoteColumnMass(source) * w(source)
    ].

Therefore any independent source-column bound can be inserted to obtain a global-`L1` estimate.

This theorem is canonical and useful as a fallback or scalar-gate interface. But it deliberately loses spatial information in `w`. It is **not** the preferred route to terminal covariance decay.

---

# 8. PR #4527 preserves the spatial geometry of the remote perturbation

PR #4527 is the current theorem-bearing frontier.

Define the canonical local propagation depth

    depth(target, mid)
      := floor(baseL1Distance(target, mid) / 2).

Define the corresponding local Green weight

    G_weight(target, mid)
      :=
    rho_local(beta)^depth(target,mid)
      / (1 - rho_local(beta)).

The repository proves every finite local resolvent entry is bounded by this weight:

    R_local,M(target, mid)
      <= G_weight(target, mid).

For a general nonnegative forcing `b`:

    G_local,M b(target)
      <=
    sum_mid G_weight(target, mid) * b(mid).

Applying this to the exact physical remote forcing gives the weighted convolution

    G_local,M(R_remote w)(target)
      <=
    sum_source [
      W_remote(target, source) * w(source)
    ],

where

    W_remote(target, source)
      :=
    sum_mid
      G_weight(target, mid)
      * R_remote(source, mid).

Thus the full singleton comparison becomes schematically

    w(target)
      <=
    rho_local^D/(1-rho_local) * amplitude
      +
    sum_source W_remote(target,source) * w(source)
      +
    rho_local^M * distanceBound.

This is strictly sharper than the #4526 global-`L1` collapse: target/intermediate base-`L1` geometry is retained all the way through the remote perturbation.

---

# 9. The present obstruction is now a weighted remote-column problem

The local Green mechanism itself is no longer the open problem.

The new central object is

    W_remote(target, source)
      =
    sum_mid
      G_weight(target, mid)
      * R_remote(source, mid).

The next analytic theorem must control this object in a way that preserves enough target/source distance information to close the terminal covariance argument.

A useful result would have one of the following shapes:

    W_remote(target, source)
      <= C_remote * q_remote^distance(target,source),

or a weighted Schur/subinvariant estimate strong enough to absorb

    sum_source W_remote(target,source) * w(source)

without collapsing back to a volume-dependent global norm.

The critical non-circularity constraint remains:

> Do not prove the weighted remote bound by assuming the same terminal covariance decay that the weighted remote bound is intended to help prove.

The already-formalized terminal-covariance-decay => uniform-remote-residual route remains downstream infrastructure, not an admissible upstream premise for this closure.

---

# 10. The fixed-target law and source-aligned perturbation route remain distinct

The source-aligned physical envelope used in #4520-#4527 and the fixed-target kernel-section envelope introduced earlier are different objects.

The repository also has a fixed-target physical left-left envelope for the exact kernel-section law:

    C5-exceptional pair
      -> Harnack coefficient,

    C5-remote pair
      -> target-specific actual remote residual.

Permanent boundary:

    source-aligned envelope
      != fixed-target kernel-section envelope.

The current route therefore still needs an explicit theorem-level connection at the point where the weighted perturbation mechanism is instantiated for the exact terminal kernel-section covariance.

No identification is assumed merely because both decompositions use local Harnack and remote terms.

---

# 11. The covariance remainder is still independently open

The covariance telescope controls

    Cov(F,G) - Cov(F,P_scan^M G),

not `Cov(F,G)` alone.

The new local comparison remainder

    rho_local(beta)^M * distanceBound

is **not** the same object as

    Cov(F,P_scan^M G).

Even though `rho_local^M` is geometrically small under `rho_local < 1`, the repository still requires a valid theorem to close or absorb the restricted-random-scan covariance remainder.

Possible valid routes include:

    P_scan^M G -> constant
      in a sufficiently strong sense,

or

    a finite closure / absorption theorem
      that directly controls Cov(F,P_scan^M G).

No such conclusion is currently inferred from the finite resolvent alone.

---

# 12. The downstream cubic-shell and uniform-residual pipeline is already ready

PRs #4479-#4494 remain valid downstream infrastructure.

Once the exact terminal kernel-section covariance satisfies a volume-uniform base-`L1` exponential bound

    |Cov(target,source)| <= C * q^distance,
    0 <= q < 1,

the repository already proves:

    terminal covariance decay
      -> terminal response decay
      -> cubic base-L1 shell summability
      -> uniform terminal shell mass
      -> explicit uniform remote residual rho
      -> strict physical sweep gate.

The source-aligned remote shell satisfies the volume-independent polynomial bound

    shellCard(r) <= 3 * (2*r + 1)^3,

so polynomial shell growth against any `q^r` with `0 <= q < 1` is summable. No artificial condition such as `18*q < 1` is needed in that downstream shell summation.

The circularity warning is essential:

    terminal covariance decay -> uniform remote residual

is a valid downstream implication,

but

    assume that uniform remote residual
      -> prove the same terminal covariance decay

would not close the proof unless an independent route supplies the residual bound.

---

# 13. Immediate next theorem route

Starting from PR #4527, the intended order is now:

    source-singleton terminal variation

      -> actual local Harnack Green weight

      -> base-L1 weighted remote convolution

      -> independent weighted-remote control
         preserving target/source spatial information

      -> explicit bridge to the exact fixed-target
         kernel-section comparison

      + restricted-random-scan covariance-remainder closure

      -> exact terminal kernel-section base-L1 covariance decay

      -> cubic shell summability

      -> uniform remote residual rho

      -> strict physical sweep contraction

      -> physical Poincare / coercivity

      -> uniform finite-volume transfer/Hamiltonian gap

      -> thermodynamic / continuum physical carrier

      -> Clay-level Yang--Mills existence + mass gap.

The immediate mathematical target is therefore **not another local-resolvent theorem**. It is a non-circular estimate on the weighted remote convolution or an equivalent weighted comparison operator.

---

# 14. Permanent semantic boundaries

These distinctions remain part of the proof discipline:

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
    finite local Green resolvent != infinite resolvent automatically
    finite local power remainder != covariance remainder
    weighted remote convolution != proved weighted remote decay
    strict finite-volume gate != uniform-in-volume gate
    uniform finite-volume gap != thermodynamic/continuum Yang--Mills mass gap.

No `sorry`, `admit`, new axioms, hidden constants, weakened hypotheses, theorem weakening, or semantic broadening are accepted as substitutes for proof.

---

## Toolchain

The formalization currently tracks Lean `v4.30.0-rc2` with the repository-pinned mathlib revision. Repository lockfiles and the exact current GitHub theorem-carrier state are authoritative over this prose.

---

## Short status

**Closed through #4527:** actual remote conditional influence; physical local/remote envelope; terminal covariance normal form and denominator floor; cubic base-`L1` shell geometry; exact kernel-section conditional expectation and `L2` projection identities; deterministic/restricted-random-scan covariance telescopes; source-singleton finite-resolvent reduction; dense-carrier spatial-flatness obstruction; plaquette-local/base-`L1` separation; sparse proxy singleton Green theorem; actual local Harnack kernel; actual local-Harnack base-`L1` propagation; actual local geometric finite resolvent; exact local-plus-remote perturbation algebra; singleton local Green reduction; remote column-mass reduction; and base-`L1` weighted remote convolution.

**Open now:** prove an independent spatial estimate or absorption principle for the weighted remote convolution, connect that mechanism to the exact fixed-target kernel-section comparison, and close the restricted-random-scan covariance remainder. Those are the immediate missing ingredients before volume-uniform terminal kernel-section covariance decay can feed the already-built uniform-residual, contraction, coercivity, finite-gap, and continuum pipelines.
