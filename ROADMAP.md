# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-24 JST

Repository: **itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline at this documentation refresh:

**73d90bb97eb1a906d1d11eec10314e1ce1feb518**

This is the merge commit of PR #4693, **Apply sharp Haar bound at ground-state sweep stages**.

The default branch **main** is not theorem authority.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A docs-only merge may advance the branch pointer without changing the theorem-bearing mathematical baseline.

---

## 0. Claim boundary

The repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

### Integrated

- finite-volume periodic Wilson / OS / physical-transfer construction;
- canonical nonnegative vacuum and ground-state transform;
- high-temperature response, influence, covariance, and shell-decay machinery;
- positive volume-independent strict physical sweep interval;
- genuine six-spatial joint-L2 residual/Rayleigh receivers;
- exact beta-zero ambient and physical rank-one transfer;
- beta-zero vacuum measure = spatial Haar;
- beta-zero ground-state joint measure = pair Haar;
- exact beta-zero physical transfer gap = 1;
- complete beta-zero six-spatial pair-Haar geometry;
- genuine beta-zero physical six-spatial constants (kappa_0=1/6), (q_0=5/6);
- six-spatial receiver consistency bound (operatorname{gap}(0)ge 1/16);
- positive-beta physical maximum-row and maximum-column closure;
- volume/background-independent bidirectional Schur coefficient (q_{m phys}<1);
- ordered one-link sweep path loss controlled by six-spatial block residual energy;
- genuine link-indexed sweep-stage local profile (ell_e);
- direct Schur receiver using that local profile;
- bounded-concrete core preservation under every one-link sweep prefix;
- sharp Haar one-link local coercivity available at every sweep stage.

### Not yet integrated

- an actual ground-state observable-specific physical profile (u_e(F));
- the one-sided inequality
  [
  u_t(F)le ell_t(F)+sum_s K_{ts}u_s(F);
  ]
- a genuine global profile majorant on the ground-state joint carrier;
- a positive-beta bounded-core six-spatial Poincare theorem;
- the resulting full-joint-L2 volume-independent positive-beta Rayleigh coefficient;
- the resulting scale-independent positive-beta physical transfer/Hamiltonian gap;
- thermodynamic/infinite-volume physical construction;
- continuum OS/Wightman Yang--Mills construction;
- final continuum mass-gap theorem.

---

## 1. Closed infrastructure: finite Wilson / OS / physical transfer

The existing foundation remains authoritative infrastructure:

~~~text
periodic Wilson action / one-slab kernel
  -> Haar L2 carriers
  -> OS reflection-positive boundary construction
  -> Gauss-law physical restriction
  -> compact positive physical transfer
  -> top eigenspace / canonical nonnegative vacuum
  -> ground-state transform
  -> vacuum and joint probability laws
  -> genuine one-link and spatial-color conditional expectations
~~~

Do not restart this layer unless a later exact artifact reveals a real obstruction.

**Status: closed as infrastructure.**

---

## 2. High-temperature physical response and influence — closed

Integrated chain:

~~~text
#4634 fixed-right target-ratio response continuity
#4637 canonical half-barrier closure
#4638 actual weighted physical influence / response decay
#4639 finite influence-path / resolvent propagation
#4640 random-scan variation contraction
#4641 finite covariance resolvent
#4642 spatial random-scan resolvent
#4643 actual spatial covariance clustering
#4644 two-step terminal covariance decay
#4645 cubic-shell summability / uniform remote residual
#4646 terminal covariance oscillation sharpening
#4647 beta-zero-vanishing sharpened remote residual
#4648 strict positive high-temperature physical sweep gate
~~~

This lane establishes a positive high-temperature interval with volume-independent physical influence/sweep contraction.

It is bounded-test / physical-influence geometry, not by itself an L2 Poincare theorem.

**Status: closed as influence-side infrastructure.**

---

## 3. Genuine ground-state L2 receiver — closed

### #4650 — bounded-core to full L2

Integrated:

- six-spatial normalized residual energy on the genuine ground-state joint L2 carrier;
- continuity of that energy;
- dense bounded-concrete core;
- coefficient-preserving closure from the core to full L2.

### #4651 — frame / random-scan / transfer-gap receiver

For the six genuine color projections (P_c),

~~~text
P_rs = (1/6) * sum_c P_c.
~~~

The Hilbert identity relates

~~~text
kappa * ||x||^2
  <= (1/6) * sum_c ||x-P_c x||^2
~~~

to

~~~text
inner(P_rs x,x)
  <= (1-kappa) * ||x||^2.
~~~

Any genuine (q<1) gives the physical transfer-gap lower bound

~~~text
3*(1-q)/8.
~~~

### #4652 — finite commuting-projection tensorization

Provides the abstract finite Hilbert tensorization receiver used by the beta-zero pair-Haar geometry.

**Status: closed as receiver infrastructure.**

---

## 4. Exact beta-zero endpoint — closed

PRs #4653-#4657 establish

~~~text
ambient transfer = |1><1|
physical transfer = |1><1|
vacuum measure = spatial Haar
ground-state joint measure = pair Haar
normalized physical transfer = 0 on top-orthogonal sector
gap_beta=0 = 1.
~~~

PRs #4662-#4676 close the literal six-spatial pair-Haar projection geometry:

- color/off-color product decomposition;
- common-fixed boundary sector;
- self-adjoint idempotent projections;
- range invariance and pairwise commutation;
- full-sweep tensorization;
- sweep as orthogonal projection;
- exact (kappa_0=1/6);
- exact (q_0=5/6).

PRs #4677-#4678 bridge the genuine physical beta-zero excitation sector into the literal pair-Haar boundary geometry.

PR #4681 packages the genuine physical beta-zero six-spatial constants.

PR #4682 transports them to the genuine ground-state carrier and feeds the existing receiver.

Canonical endpoint receipts:

~~~text
kappa_0 = 1/6
q_0 = 5/6
gap(0) >= 1/16
gap(0) = 1.
~~~

The (1/16) bound is non-optimal and retained only as a consistency check of the six-spatial route.

PR #4675 remains **closed / unmerged / superseded by #4676**.

**Status: closed.**

---

## 5. Positive-beta bidirectional Schur L2 — closed

### #4683 — generic theorem

For a finite nonnegative influence matrix, simultaneous row and column control gives a genuine L2 Schur estimate.

### #4684 — remote-row obstruction isolated

The actual physical envelope is decomposed into

~~~text
local Harnack part + source-aligned remote residual.
~~~

The missing directional row sum was named explicitly rather than hidden behind symmetry.

### #4685 — physical row/column Schur gate

Combines the physical row and column estimates with the generic bidirectional Schur theorem.

### #4686 — remote row closed

Oscillation covariance decay, represented-right transport, fixed-target source shells, and cubic shell summability close the remote row uniformly.

No symmetry of the remote residual is assumed.

### #4687 — uniform coefficient

Defines the volume/background-independent scalar

~~~text
q_phys(s,beta)
  = 18 * eta(beta) + rho_osc(s,beta)
~~~

and proves on the canonical strict interval

~~~text
0 <= q_phys < 1
maxRow(K) <= q_phys
maxColumn(K) <= q_phys.
~~~

Therefore

~~~text
sum_t (sum_s K_ts v_s)^2
  <= q_phys^2 * sum_s v_s^2.
~~~

And for nonnegative (u,ell) satisfying

~~~text
u_t <= ell_t + sum_s K_ts u_s,
~~~

Lean proves

~~~text
(1-q_phys)^2 * sum_t u_t^2
  <= sum_t ell_t^2.
~~~

**Status: matrix / Schur / resolvent side closed.**

---

## 6. Sweep local-energy bridge — closed

### #4688 — generic nested-block theorem

For a real Hilbert space, if a block projection (B) absorbs every projection (P_c) appearing in an ordered sweep,

~~~text
B(P_c x) = Bx,
~~~

then no pairwise commutativity is required to prove

~~~text
PathLoss(P,cs,x) <= ||x-Bx||^2.
~~~

### #4689 — genuine six-spatial specialization

For one fixed spatial color (c),

~~~text
PathLoss_c(f) <= ||f-P_c f||^2.
~~~

Averaging over six colors:

~~~text
(1/6) * sum_c PathLoss_c(f)
  <= E_6sp(f).
~~~

No same-color independence and no positive-beta same-color commutativity assumption are introduced.

### #4690 — link-indexed local profile

Defines a nonnegative sweep-stage local amplitude (ell_e(f)) from the actual successive projection defects.

Exact identity:

~~~text
(1/6) * sum_e ell_e(f)^2
  = SixSpatialOneLinkSweepPathLoss(f)
  <= E_6sp(f).
~~~

The profile is indexed by genuine spatial links and contains no volume-dependent color-class multiplicity.

**Status: closed.**

---

## 7. Concrete Schur receiver with sweep-stage local profile — closed

PR #4691 feeds the #4690 local profile directly into #4687.

For every nonnegative profile (u) satisfying

~~~text
u_t <= ell_t(f) + sum_s K_ts u_s,
~~~

Lean proves

~~~text
(1/6) * (1-q_phys)^2 * sum_e u_e^2
  <= E_6sp(f).
~~~

A relative-Poincare wrapper is also present. Its only additional premise is the explicit global majorant

~~~text
||f-center(f)||^2 <= sum_e u_e^2.
~~~

This theorem deliberately does **not** assert that such a profile already exists.

**Status: receiver closed; observable-specific premises remain open.**

---

## 8. Bounded-concrete sweep invariance — closed

The sharp one-link theorem acts on bounded strongly measurable concrete representatives. To apply it at sweep stages, those stages must remain in the bounded-concrete core.

PR #4692 proves:

~~~text
f in boundedConcreteCore
  -> one-link condExpL2(f) in boundedConcreteCore
  -> every finite same-color sweep stays in boundedConcreteCore
  -> every canonical sweep prefix stays in boundedConcreteCore.
~~~

Proof architecture:

1. choose the ordinary conditional expectation representative on the retained sigma-algebra;
2. prove its essential bound using `condExp_mono` and `condExp_const`;
3. replace it on a null set by an everywhere-bounded measurable representative;
4. identify its L2 class with the genuine `condExpL2` projection through `MemLp.condExpL2_ae_eq_condExp`;
5. induct through a finite sweep.

This avoids pointwise evaluation of arbitrary L2 quotient representatives.

**Status: closed.**

---

## 9. Stagewise sharp Haar local coercivity — closed

PR #4693 combines #4692 with the existing sharp bounded-core one-link theorem.

For a bounded-concrete initial vector, any fixed-color sweep prefix (cs), and any chosen next link (e), the stage vector

~~~text
x_cs = P_cs ... P_c1 f
~~~

has an explicit bounded strongly measurable representative (F_{cs}) satisfying

~~~text
SharpHaarVarianceFunctional(F_cs,e)
  <= ENNReal.ofReal (||x_cs - P_e x_cs||^2).
~~~

The exact (e^{-16eta}) sharp Haar coefficient remains encoded in the existing sharp Haar functional.

The canonical `Finset.univ.toList.take k` prefix form required by the #4690 sweep is packaged explicitly.

**Status: closed.**

---

## 10. Immediate next theorem — actual ground-state physical hybrid one-sided profile

This is the active mathematical frontier.

### Do not restart the hybrid machinery

The older integrated raw Wilson spine #852-#906 already contains:

- canonical finite hybrid path;
- independent-pair hybrid increment/profile;
- native conditional-pair reference;
- hybrid/native endpoint laws;
- source-overlap transport;
- target trajectory;
- Gibbs-indexed trajectory kernel;
- endpoint coupling;
- double trajectory;
- endpoint cross moment;
- conditional covariance / conditional variance decomposition.

Reuse these artifacts. Do not recreate an independent coupling stack.

### Goal

For a bounded concrete observable (F), construct a genuine nonnegative profile

~~~text
u_e(F)
~~~

on

~~~text
PeriodicHypercubicEvenSpatialSliceLink H
~~~

and prove, for every target link,

~~~text
u_t(F)
  <= ell_t(F)
     + sum_s K_ts u_s(F),
~~~

where

- (K) is the actual physical influence envelope from #4687;
- (ell_t(F)) is the #4690 sweep-stage local profile;
- #4692 ensures each sweep stage stays in the bounded-concrete core;
- #4693 supplies sharp Haar local coercivity at those stages.

### Acceptance criterion

A theorem with:

- actual ground-state / physical conditional-law objects;
- actual physical envelope (K);
- no new ad hoc volume-dependent coefficient;
- no hidden same-color independence or interacting commutativity assumption;
- no replacement of L2 statements by bounded-test/TV statements.

**Status: open.**

---

## 11. Second active theorem — genuine global profile majorant

After the actual (u_e(F)) is constructed, prove a global comparison of the form

~~~text
||F-center(F)||_L2^2
  <= sum_e u_e(F)^2
~~~

or an equivalent independent-pair energy inequality on the correct ground-state joint carrier.

### Existing input

The raw Wilson canonical hybrid pair profile already has a global pair majorant.

### Main danger

The naive finite hybrid telescoping bound carries an edge-cardinality Cauchy factor. Reusing it blindly would reintroduce a volume-dependent constant and destroy the desired uniform gap.

The ground-state/sweep formulation must exploit the current stagewise local structure rather than simply importing that finite cardinality loss.

### Acceptance criterion

A genuine ground-state global majorant compatible with the #4691 Schur receiver and with no unacceptable volume factor.

**Status: open.**

---

## 12. Positive-beta bounded-core Poincare target

Once Sections 10 and 11 are closed, #4691 gives a bounded-core estimate.

Schematic chain:

~~~text
global centered energy
  <= sum_e u_e^2
  <= (1-q_phys)^(-2) * sum_e ell_e^2
  <= 6 * (1-q_phys)^(-2) * E_6sp.
~~~

Equivalently, before final normalization choices,

~~~text
positive coefficient * ||F-center(F)||^2
  <= E_6sp(F).
~~~

Do **not** freeze the final coefficient until the actual (u_e) normalization and sharp Haar factor are formally connected.

**Status: open, but all abstract receivers are ready.**

---

## 13. Full genuine joint L2 and physical transfer gap

After a bounded-core positive-beta Poincare theorem:

1. apply #4650 to extend the coefficient to full genuine joint L2;
2. use #4651 to obtain the corresponding six-spatial Rayleigh (q(eta)<1);
3. feed the physical transfer-gap receiver;
4. obtain a finite-volume gap lower bound independent of volume on the selected positive-beta interval;
5. transport to the exact Hamiltonian normalization and vacuum-orthogonal sector.

This remains a lattice theorem, not yet the continuum mass gap.

---

## 14. Thermodynamic / infinite-volume physical construction

After a uniform finite-volume physical gap:

1. formalize compatible finite-volume embeddings/restrictions;
2. prove consistency of vacuum states and observables;
3. establish the chosen compactness/projective/direct-limit mechanism;
4. construct the infinite-volume Euclidean physical state;
5. preserve reflection positivity, gauge invariance, clustering, and nontrivial observable content.

**Status: downstream.**

---

## 15. Continuum OS / Wightman construction

Required downstream units include:

- continuum Euclidean invariance;
- reflection positivity;
- regularity sufficient for OS reconstruction;
- decay/clustering compatible with spectral interpretation;
- nontrivial physical Hilbert space and observable algebra;
- Wightman/OS reconstruction on the same-root theory.

**Status: downstream.**

---

## 16. Continuum mass gap

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

The finite-volume gap must survive every limiting and identification step actually used.

A fixed-volume eigenvalue, an auxiliary transfer matrix, or an unrelated continuum limit is insufficient.

**Status: downstream / not yet proved.**

---

## 17. Recent canonical theorem units

| PR | Status | Role |
| --- | --- | --- |
| #4681 | merged | exact genuine beta-zero physical six-spatial frame/Rayleigh package |
| #4682 | merged | beta-zero transport to genuine ground-state L2 and 1/16 receiver consistency |
| #4683 | merged | generic bidirectional Schur L2 theorem |
| #4684 | merged | physical remote-row obstruction isolated |
| #4685 | merged | physical row/column -> bidirectional Schur gate |
| #4686 | merged | remote row closed by oscillation covariance decay |
| #4687 | merged | volume-independent uniform (q_{m phys}) and Schur receiver |
| #4688 | merged | nested block projection dominates sweep path loss |
| #4689 | merged | genuine six-color one-link path loss <= six-spatial residual |
| #4690 | merged | link-indexed sweep-stage local profile |
| #4691 | merged | concrete local profile fed into uniform Schur receiver |
| #4692 | merged | bounded-concrete core invariant under one-link sweeps |
| #4693 | merged | stagewise sharp Haar local coercivity |
| #4675 | closed / unmerged | superseded by #4676 |

Recent exact-head validation:

- #4689: `ca362fd5305d833541bad53833fbaeea637eb4b8` — Fast Check #14896 / run 35925136137: success.
- #4690: `8788b40b4a70aefe3ed7b5f45064c01a00f39ec2` — Fast Check #14899 / run 35929374564: success.
- #4691: `0ab14ea94146adf3c35328d23aca5d36d8d2fdb8` — Fast Check #14901 / run 35929862853: success.
- #4692: `82adb2203f0fdf3a1be38804be441e13d926eee8` — Fast Check #14908 / run 35932670460: success.
- #4693: `9ab9afc48a411529f7ba50b2c79cb9b2cda63066` — Fast Check #14910 / run 35933345632: success.

Current theorem-bearing baseline before this docs refresh:

**73d90bb97eb1a906d1d11eec10314e1ce1feb518**

---

## 18. Lean 4 / mathlib engineering rules

Pinned environment:

- Lean v4.30.0-rc2
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Operational rules:

1. inspect the whole changed module, CompileSmoke, import graph, and dependent API when CI fails;
2. do not infer mathematical failure from a single elaboration message before checking exact types and imports;
3. treat the pinned mathlib revision as authority rather than current master;
4. keep dependent Lp measure transport narrow;
5. distinguish retained and ambient measurable spaces explicitly in conditional-expectation proofs;
6. remember that local `MeasurableSpace` definitions can participate in typeclass inference; restore the intended ambient instance explicitly when necessary;
7. use ordinary `condExp` representatives only through measurable/a.e. identities; do not pointwise evaluate arbitrary L2 quotient representatives;
8. use `MemLp.condExpL2_ae_eq_condExp` for the L2/ordinary conditional-expectation bridge;
9. use typed `simpa using` for dependent Sigma reindexing when `rw` does not syntactically match;
10. normalize finite color indices to `Fin 6` early when required by receivers;
11. remember that `rw` may finish a goal; do not append an unconditional `rfl`;
12. inspect `add_le_add_left/right` by type, not by name;
13. validate the exact PR head, workflow completion, and exact-head commit-status receipt before merge;
14. after docs-only merges, separate current branch pointer from the last theorem-bearing merge.

---

## 19. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe `formal/real-hilbert-uniform-coercive-strong-limit`;
2. expected theorem-bearing baseline is `73d90bb97eb1a906d1d11eec10314e1ce1feb518`, unless a later theorem merge has occurred;
3. if a docs-only merge follows this refresh, keep the theorem baseline distinct from the current pointer;
4. retain #4687 as the uniform physical Schur authority;
5. retain #4690 as the link-indexed local-profile authority;
6. retain #4691 as the concrete Schur/Poincare receiver;
7. retain #4692 as bounded-concrete sweep-invariance authority;
8. retain #4693 as stagewise sharp Haar local-coercivity authority;
9. reuse #852-#906 rather than rebuilding hybrid/trajectory probability geometry;
10. construct the actual bounded-concrete ground-state physical profile (u_e(F));
11. prove the one-sided inequality against the actual physical envelope (K);
12. then prove the global profile majorant without a volume factor;
13. feed the results through #4691 -> #4650 -> #4651 toward a positive-beta volume-independent physical gap.

The immediate theorem unit is:

**Ground-state bounded-concrete physical hybrid one-sided profile.**
