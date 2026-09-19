# MGAP4D Roadmap

This roadmap records the theorem architecture and current development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-19 JST**.

The authoritative theorem-carrier branch is:

    formal/real-hilbert-uniform-coercive-strong-limit

The exact theorem-bearing baseline used for this refresh is:

    7e07ea2d7579839f20d08559b39dcb397bf42ebc

This is the merge commit of PR #4527:

    Preserve base-L1 geometry in remote local-Green convolution

This ROADMAP update is documentation-only. After its merge, the branch pointer may advance, while the theorem-bearing mathematical baseline remains the latest theorem-bearing merge unless another theorem PR lands first.

Authority order:

    1. exact current GitHub theorem-carrier SHA
    2. formal Lean theorem artifacts
    3. README / ROADMAP
    4. CI/runtime receipts
    5. historical summaries or memory

`main` is not theorem authority when histories differ.

---

# Current dependency graph

    A. FINITE PERIODIC WILSON / OS ROOT                          [INTEGRATED]
       -> compact SU(N) finite lattice
       -> reflection positivity / OS carriers
       -> one-slab transfer and ground-state structure
       -> conditional-expectation / coercivity interfaces

    B. CONTINUOUS C5 ONE-LINK REFERENCE LAW                     [INTEGRATED]
       -> normalized fiber probability law
       -> measurable heat-bath kernel
       -> stationarity / properness
       -> represented-source cancellation

    C. LOCAL GEOMETRY                                            [INTEGRATED]
       -> intrinsic active-neighbor degree <= 18
       -> C5 exceptional set <= 20
       -> periodic active graph
       -> canonical link-base L1 geometry

    D. FIXED-RIGHT / CROSS-RATIO REMOTE CONTROL                 [INTEGRATED]
       -> target-ratio response
       -> targetwise worst-case majorants
       -> actual remote conditional influence
       -> concrete remote residual kernel

    E. PHYSICAL LOCAL + REMOTE ENVELOPE                          [INTEGRATED]
       -> source-aligned active Harnack + remote residual
       -> fixed-target exact physical envelope
       -> finite-volume physical comparison interfaces

    F. UNIFORM REMOTE-RESIDUAL REDUCTION                         [INTEGRATED]
       -> two-step terminal normal form
       -> crossing denominator floor
       -> cubic base-L1 shell bound
       -> terminal covariance decay => uniform residual rho
                                                                  [DOWNSTREAM]

    G. EXACT KERNEL-SECTION L2 / COVARIANCE STRUCTURE             [INTEGRATED]
       -> remote one-link conditional expectation
       -> L2 projection / fluctuation
       -> covariance self-adjointness
       -> one-link covariance Dirichlet identity

    H. COVARIANCE TELESCOPES                                     [INTEGRATED]
       -> deterministic schedule telescope
       -> tagged variation propagation
       -> restricted random-scan covariance identity
       -> finite iterate transport
       -> finite resolvent covariance bound

    I. SOURCE-LOCALIZED TERMINAL RESOLVENT                        [INTEGRATED #4515]
       -> source crossing variation is singleton-supported
       -> terminal finite-resolvent pairing collapses to one source entry

    J. DENSE-CARRIER SPATIAL OBSTRUCTION                          [INTEGRATED #4516]
       -> coarse off-fiber one-step profile is flat off target
       -> different base-L1 radii receive the same coarse coefficient
       -> dense carrier cannot be the final spatial-decay mechanism

    K. PLAQUETTE-LOCAL TO BASE-L1 BRIDGE                         [INTEGRATED #4518]
       -> one local step changes base-L1 distance by <= 2
       -> d-step local path changes distance by <= 2d
       -> distance >= 2D gives local propagation separation D

    L. SPARSE SINGLETON PROXY RESOLVENT                           [INTEGRATED #4519]
       -> singleton forcing
       -> separated finite-resolvent geometric tail
       -> proxy/model theorem only

    M. ACTUAL PHYSICAL LOCAL HARNACK KERNEL                       [INTEGRATED #4520-#4521]
       -> exact active-neighbor local kernel
       -> physical envelope = local Harnack + remote residual
       -> row/column mass <= rho_local
       -> powers have exact base-L1 finite propagation

    N. ACTUAL LOCAL HARNACK FINITE GREEN                         [INTEGRATED #4523]
       -> finite Neumann resolvent of K_local
       -> exact prefix vanishing below propagation depth
       -> geometric base-L1 bound rho_local^D/(1-rho_local)

    O. LOCAL + REMOTE PERTURBATION                               [INTEGRATED #4524]
       -> w <= v + (K_local + R_remote)w
       -> remote term retained as explicit forcing
       -> finite local remainder retained explicitly

    P. SINGLETON SOURCE THROUGH LOCAL GREEN                       [INTEGRATED #4525]
       -> generic kernel powers matched to local-Harnack iterates
       -> singleton direct term inherits base-L1 geometric decay
       -> remainder = local Green(remote forcing) + local power remainder

    Q. REMOTE COLUMN-MASS REDUCTION                              [INTEGRATED #4526]
       -> local Green <= inverse local gap * forcing L1 mass
       -> remote forcing mass = weighted remote source-column pairing
       -> global-L1 reduction available as coarse fallback

    R. BASE-L1 WEIGHTED REMOTE CONVOLUTION                       [INTEGRATED #4527]
       -> arbitrary local resolvent decomposes sourcewise
       -> canonical local Green weight at floor(baseL1Distance/2)
       -> local Green(remote forcing) retains intermediate-link geometry
       -> weighted remote column W_remote(target,source)

    S. WEIGHTED REMOTE CONTROL                                   [OPEN NOW]
       -> prove decay / weighted Schur / subinvariant control for W_remote
       -> preserve target/source spatial information
       -> do not assume the final terminal covariance decay

    T. FIXED-TARGET KERNEL-SECTION INSTANTIATION                 [OPEN NEXT]
       -> connect source-aligned perturbation machinery to the exact
          fixed-target kernel-section comparison
       -> no silent identification of the two envelopes

    U. RANDOM-SCAN COVARIANCE REMAINDER                          [OPEN NEXT]
       -> control Cov(F, P_scan^M G)
       -> justify M -> infinity or an equivalent finite absorption
       -> finite resolvent alone is insufficient

    V. EXACT TERMINAL KERNEL-SECTION COVARIANCE DECAY             [OPEN]
       -> combine R + S + T + U
       -> prove volume-uniform base-L1 exponential decay

    W. UNIFORM PHYSICAL RESIDUAL / SWEEP GATE                     [OPEN DOWNSTREAM]
       -> existing cubic shell theorem gives uniform rho
       -> strict physical column gate
       -> volume-independent full-sweep contraction

    X. PHYSICAL POINCARE / COERCIVITY                             [OPEN DOWNSTREAM]

    Y. UNIFORM FINITE-VOLUME PHYSICAL GAP                         [OPEN DOWNSTREAM]

    Z. THERMODYNAMIC / CONTINUUM PHYSICAL LIMIT                  [OPEN DOWNSTREAM]

    AA. CLAY-LEVEL EXISTENCE + MASS GAP                           [OPEN]

---

# Phase 0 — Authority and proof discipline

**Status: integrated and permanent.**

For theorem-bearing work:

    fresh-fetch theorem-carrier
    -> lock exact canonical SHA
    -> inspect exact Lean interfaces and the full changed file
    -> state one mathematically coherent theorem unit
    -> push and observe the PR current head
    -> query CI for that exact head
    -> repair the first genuine Lean/API/syntax error without weakening
    -> require completed/success on the exact current head
    -> merge against the expected head SHA
    -> fresh-fetch canonical again.

A stale run attached to an older branch head is not CI authority for a moved PR.

Queued or in-progress CI is not GREEN.

No new `sorry`, `admit`, axioms, hidden constants, assumption weakening, theorem weakening, or semantic broadening may be introduced as a substitute for proof.

---

# Phase 1 — Finite Wilson root and OS infrastructure

**Status: integrated.**

The finite periodic compact-`SU(N)` Wilson model, reflection-positive structures, one-slab transfer operators, nonnegative ground-state architecture, and downstream coercivity/spectral interfaces form the theorem root.

Boundary: this is not by itself a continuum Yang--Mills existence theorem.

---

# Phase 2 — Continuous one-link law and local C5 geometry

**Status: integrated.**

The repository contains the exact normalized continuous one-link law, measurable conditional kernel, full-configuration heat-bath reinsertion, stationarity, and C5 geometry.

Key volume-independent local facts:

    active spatial plaquette-neighbor degree <= 18
    C5 exceptional set cardinality <= 20.

The old dense distinct-fiber carrier remains a legitimate coarse upper bound, but it is not the actual sparse physical carrier.

---

# Phase 3 — Actual remote conditional influence

**Status: integrated through #4464-#4469.**

For geometrically remote target/source pairs, the normalized one-link bounded-test conditional-law response is controlled by a targetwise worst-case cross-ratio majorant.

The source column is packaged as a concrete nonnegative remote residual.

This closes the old gap:

    fixed-right response
      -> actual remote conditional-law influence.

---

# Phase 4 — Physical local-plus-remote envelopes

**Status: integrated through #4470-#4478, #4517, #4520.**

The actual source-aligned physical influence decomposes into:

    intrinsic active-neighbor Harnack contribution
    + source-aligned remote physical residual.

The exact fixed-target kernel-section law also has its own local/remote physical envelope.

Permanent distinction:

    source-aligned physical envelope
      != fixed-target kernel-section envelope.

The two may only be identified or transported through an explicit theorem.

---

# Phase 5 — Uniform remote residual reduction

**Status: integrated through #4479-#4494.**

The remote uniformity problem is isolated in an explicit certificate.

The nonlocal part is reduced to a two-step terminal quantity, and the exact terminal response is normalized to a covariance under the fixed-`k` ground-state kernel-section law.

The crossing denominator obeys:

    crossingExpectation >= exp(-2 * beta),

hence:

    terminalResponseAbs
      <= exp(2 * beta) * |kernelSectionCovariance|.

The source-aligned remote base-`L1` shell satisfies:

    shellCard(r) <= 3 * (2*r + 1)^3.

The cubic shell majorant times `q^r` is summable for every `0 <= q < 1`.

Therefore:

    volume-uniform exponential terminal covariance decay
      -> uniform terminal shell mass
      -> uniform remote residual rho
      -> uniform physical sweep coefficient.

All arrows after the covariance-decay input are formalized.

Important directionality:

    covariance decay -> uniform remote residual

is downstream. It must not be used circularly as the upstream proof of the same covariance decay.

---

# Phase 6 — Exact kernel-section conditional expectation and L2 structure

**Status: integrated through #4495-#4506.**

For remote target/source geometry, the actual kernel-section one-link update is identified with conditional expectation onto the off-fiber sigma-algebra.

Consequences include:

    one-link stationarity
    MemLp 2 preservation
    covariance self-adjointness
    Q = I - P fluctuation structure
    projection idempotence
    P(Qf) = 0 a.e.
    covariance orthogonal decomposition
    one-link covariance Dirichlet identity.

No full Gibbs-law identification is assumed.

---

# Phase 7 — Deterministic and restricted-random-scan covariance telescopes

**Status: integrated through #4507-#4513.**

The one-link Dirichlet identity is telescoped through deterministic schedules and restricted random scan.

The finite covariance estimate has schematic form:

    |Cov(F,G) - Cov(F,P_scan^M G)|
      <= finite resolvent pairing.

Boundary:

    finite M
      != infinite resolvent
      != vanishing covariance remainder.

This distinction remains active.

---

# Phase 8 — Source-singleton terminal localization

**Status: integrated through #4515.**

The source crossing-ratio variation is supported on exactly one physical source fiber.

Therefore the generic finite-resolvent pairing collapses to one source coordinate.

This is the point where a spatially localized Green mechanism becomes useful.

---

# Phase 9 — Dense off-fiber obstruction

**Status: integrated through #4516.**

The coarse distinct-fiber restricted-scan carrier is proved spatially flat off target after one step.

Development consequence:

> Do not try to prove spatial covariance decay by repeatedly refining the same distance-blind dense carrier.

The route must separate genuine local propagation from the remote vacuum residual.

---

# Phase 10 — Plaquette-local propagation versus base-L1 distance

**Status: integrated through #4518.**

One actual Wilson-plaquette-local step changes periodic link-base `L1` distance by at most two.

A chain of `d` local steps therefore satisfies:

    endpoint distance <= 2*d.

Thus:

    2*D <= baseL1Distance(target, source)

gives at least `D` steps of local propagation separation.

---

# Phase 11 — Sparse Dobrushin singleton proxy

**Status: integrated through #4519.**

The sparse proxy lane proves the expected singleton geometric resolvent mechanism.

Permanent boundary:

    sparse Dobrushin proxy coefficient
      != physical background-update Harnack coefficient.

The proxy theorem is a reusable model lemma, not the physical terminal result.

---

# Phase 12 — Actual physical local Harnack kernel and finite propagation

**Status: integrated through #4520-#4521.**

The actual local physical kernel is

    K_local(target, source)
      = eta_local(beta)  on intrinsic active neighbors
      = 0                otherwise.

Define:

    rho_local(beta) := 18 * eta_local(beta).

The local kernel is symmetric; row and column masses satisfy:

    mass <= rho_local(beta).

Recursive powers obey:

    rowMass(K_local^d) <= rho_local(beta)^d,

and

    K_local^d(target, source) != 0
      -> baseL1Distance(target, source) <= 2*d.

Hence if

    2*D <= baseL1Distance(target, source),

then:

    K_local^d(target, source) = 0

for every `d < D`.

---

# Phase 13 — Actual local Harnack finite Green / resolvent

**Status: integrated through #4523.**

The finite local Neumann resolvent is now formalized directly in the continuous-vacuum lane.

Base-`L1` separation removes every degree below the propagation depth exactly.

Under

    rho_local(beta) < 1,

the finite local resolvent obeys, uniformly in `M`:

    R_local,M(target, source)
      <= rho_local(beta)^D / (1-rho_local(beta))

whenever

    2*D <= baseL1Distance(target, source).

The old Phase-15 task of “sum the actual local powers” is therefore closed.

---

# Phase 14 — Exact local-plus-remote perturbation algebra

**Status: integrated through #4524.**

Starting from

    w <= v + (K_local + R_remote)w,

the proof is reorganized as

    w <= (v + R_remote w) + K_local w.

Only `K_local` is iterated.

For finite truncation:

    w
      <= G_local,M v
        + G_local,M(R_remote w)
        + K_local^M w.

The local power remainder is bounded by:

    rho_local(beta)^M * distanceBound.

No smallness of `R_remote` is assumed.

---

# Phase 15 — Singleton source through the actual local Green operator

**Status: integrated through #4525.**

Generic finite kernel powers are identified with the recursive actual local-Harnack powers on singleton forcing.

Therefore the source-local direct term inherits the #4523 spatial Green bound:

    G_local,M(singleton_source * a)(target)
      <= rho_local^D/(1-rho_local) * a.

The full comparison becomes:

    w(target)
      <= rho_local^D/(1-rho_local) * a
        + G_local,M(R_remote w)(target)
        + rho_local^M * distanceBound.

This is now the canonical local-plus-remote comparison normal form.

---

# Phase 16 — Remote forcing reduced to source-column mass

**Status: integrated through #4526.**

For nonnegative forcing:

    G_local,M b(target)
      <= 1/(1-rho_local) * sum b.

The total physical remote forcing is exactly:

    sum_target (R_remote w)(target)
      =
    sum_source [
      remoteColumnMass(source) * w(source)
    ].

Hence an independently supplied remote-column bound gives a global-`L1` estimate.

This route is useful for scalar contraction interfaces, but it erases spatial localization and is not the preferred covariance-decay route.

---

# Phase 17 — Base-L1 weighted remote convolution

**Status: integrated through #4527.**

This phase replaces the global-`L1` collapse by a spatially resolved estimate.

Define the canonical local propagation depth:

    depth(target, mid)
      := floor(baseL1Distance(target,mid) / 2).

Define:

    G_weight(target, mid)
      :=
    rho_local^depth(target,mid) / (1-rho_local).

The repository proves:

    R_local,M(target, mid)
      <= G_weight(target, mid),

and, for any nonnegative forcing `b`:

    G_local,M b(target)
      <=
    sum_mid G_weight(target,mid) * b(mid).

For the exact physical remote forcing, define:

    W_remote(target, source)
      :=
    sum_mid
      G_weight(target,mid)
      * R_remote(source,mid).

Then:

    G_local,M(R_remote w)(target)
      <=
    sum_source W_remote(target,source) * w(source).

The singleton comparison is therefore:

    w(target)
      <=
    rho_local^D/(1-rho_local) * amplitude
      +
    sum_source W_remote(target,source) * w(source)
      +
    rho_local^M * distanceBound.

This is the current theorem-bearing frontier.

---

# Phase 18 — Control the weighted remote column

**Status: OPEN NOW.**

The immediate object is:

    W_remote(target, source)
      =
    sum_mid
      G_weight(target,mid)
      * R_remote(source,mid).

The next theorem should preserve target/source spatial information.

Preferred outputs include one of:

    W_remote(target,source)
      <= C_remote * q_remote^distance(target,source),

or

    a weighted Schur/subinvariant estimate
      strong enough to absorb
      sum_source W_remote(target,source) * w(source)

in a spatial norm.

The proof must be independent of the final terminal covariance-decay statement.

The existing terminal-covariance-decay => remote-uniform-bound theorem is not an admissible upstream shortcut here.

Possible ingredients to inspect next:

    source-aligned remote support geometry
    existing arbitrary-step remote transport formulas
    triangle inequalities for base-L1 distance
    convolution of local geometric weight with remote shell structure
    weighted operator norms that preserve exponential profiles.

---

# Phase 19 — Instantiate the weighted route for the exact fixed-target kernel-section law

**Status: OPEN NEXT.**

The terminal covariance uses an exact fixed-target kernel-section law, while #4520-#4527 primarily organize the source-aligned physical envelope.

These are not definitionally interchangeable.

Required next bridge:

    source-aligned weighted perturbation mechanism
      -> exact fixed-target kernel-section comparison,

with the target-dependent remote residual kept explicit.

No source-aligned/fixed-target identification should be introduced without proof.

---

# Phase 20 — Resolve the restricted-random-scan covariance remainder

**Status: OPEN NEXT.**

The covariance telescope controls:

    Cov(F,G) - Cov(F,P_scan^M G),

not `Cov(F,G)` directly.

A valid closure needs one of:

    P_scan^M G -> constant
      in a sufficiently strong sense,

or

    a finite absorption theorem
      directly controlling Cov(F,P_scan^M G).

Important distinction:

    rho_local^M * distanceBound

from the local comparison is not the same object as the covariance remainder.

The repository still needs a theorem for the latter.

---

# Phase 21 — Exact terminal kernel-section base-L1 covariance decay

**Status: OPEN AFTER PHASES 18-20.**

Target schematic form:

    |Cov_mu(crossing_source, terminal_target)|
      <= C * q^baseL1Distance(target,source),

uniformly in periodic volume, with:

    C >= 0,
    0 <= q < 1.

The intended proof architecture is now:

    source-singleton variation
      -> actual local Green decay
      -> weighted remote convolution
      -> independent weighted-remote control
      -> fixed-target kernel-section bridge
      + covariance-remainder closure
      -> terminal covariance decay.

---

# Phase 22 — Close uniform remote residual and physical sweep gate

**Status: OPEN DOWNSTREAM.**

Once Phase 21 is proved, the already-integrated cubic-shell theorem gives a volume-uniform remote residual scalar.

Then the source-aligned physical contraction route reduces to a strict gate schematically:

    18 * eta_local(beta) + rho_remote(beta) < 1.

The older `20 * eta + rho` C5-exceptional interface belongs to a different decomposition and must not be conflated with this 18-neighbor local-Harnack route.

---

# Phase 23 — Physical Poincare / coercivity

**Status: OPEN DOWNSTREAM.**

After uniform physical sweep contraction:

    strict physical response control
      -> conditional/block variance control
      -> Poincare / coercivity
      -> transfer-sector estimate.

The target is a volume-independent coercive constant.

---

# Phase 24 — Uniform finite-volume transfer/Hamiltonian gap

**Status: OPEN DOWNSTREAM.**

The required output is a positive lower bound uniform over the finite periodic volumes used in the limiting construction.

A gap whose constant collapses with volume is insufficient.

---

# Phase 25 — Thermodynamic / continuum physical limit

**Status: OPEN DOWNSTREAM.**

After a uniform finite-volume physical gap is established, the remaining program includes:

    compatible limiting physical states
      -> same-root OS/Wightman carrier
      -> limiting semigroup / Hamiltonian
      -> sufficiently rich nontrivial 4D Yang--Mills field/state
      -> spectral lower bound above the vacuum.

The existing scalar continuum OS lane is same-root infrastructure, not a substitute for the full gauge-field construction.

---

# Phase 26 — Clay-level target

**Status: OPEN.**

The final target remains a mathematically complete four-dimensional Yang--Mills existence and mass-gap construction in the intended setting.

The repository's current analytic frontier is substantially sharper than at #4513 or #4521:

    local finite propagation is explicit,
    the actual local Green tail is proved,
    the exact remote perturbation is separated,
    singleton forcing is localized,
    and the remote term now retains base-L1 geometry through a weighted convolution.

What remains is no longer “find a local spatial mechanism.” The local mechanism is formalized. The present task is to prove an independent spatial estimate for the weighted remote operator and to close the separate covariance remainder.

---

# Immediate theorem-development checklist

Starting from theorem-bearing baseline #4527:

    1. analyze
         W_remote(target,source)
           = sum_mid
               G_weight(target,mid)
               * R_remote(source,mid);

    2. prove a target/source spatial bound or weighted operator estimate
       for W_remote without assuming terminal covariance decay;

    3. preserve base-L1 geometry through the source-aligned remote support
       and any shell/transport decomposition used in step 2;

    4. connect the weighted perturbation mechanism to the exact
       fixed-target kernel-section law by an explicit theorem;

    5. close or quantitatively absorb
         Cov(F, P_scan^M G);

    6. prove the exact terminal kernel-section covariance-decay predicate;

    7. invoke the existing cubic shell theorem to obtain uniform rho_remote;

    8. close the strict physical sweep gate;

    9. derive physical Poincare/coercivity;

    10. derive a volume-uniform finite-volume transfer/Hamiltonian gap;

    11. advance the thermodynamic/continuum physical Yang--Mills carrier;

    12. only then close the Clay-level existence and mass-gap statement.

---

# Current conceptual transition

    #4513:
      finite restricted-random-scan covariance resolvent

    #4515:
      source variation becomes singleton-supported

    #4516:
      old coarse distinct-fiber propagation is shown
      to erase spatial radius information

    #4518:
      plaquette-local propagation is connected to
      canonical periodic link-base L1 distance

    #4519:
      sparse proxy demonstrates the geometric Green-tail mechanism

    #4520-#4521:
      actual physical local Harnack kernel is extracted,
      and its powers acquire exact base-L1 finite propagation

    #4523:
      actual local powers are summed into the geometric finite Green tail

    #4524:
      full physical comparison is reorganized through local Green
      with the exact remote residual left as forcing

    #4525:
      singleton direct forcing inherits actual local base-L1 decay

    #4526:
      remote Green forcing is reduced to weighted source-column mass,
      with a coarse global-L1 fallback

    #4527:
      the global-L1 collapse is refined to a base-L1 weighted
      target/intermediate/source remote convolution

    current frontier:
      prove non-circular spatial control of the weighted remote column,
      instantiate it for the exact fixed-target kernel-section law,
      and resolve the covariance remainder.
