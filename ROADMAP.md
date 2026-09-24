# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-24 JST

Repository:

**itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline at this documentation refresh:

**f22fbd1db7325dfe2da08e90b278b3bd14976b89**

This is the merge commit of PR #4704, **Apply physical RMS Harnack to bounded-concrete ground-state sections**.

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
- genuine beta-zero six-spatial constants kappa_0 = 1/6 and q_0 = 5/6;
- six-spatial receiver consistency bound gap(0) >= 1/16;
- positive-beta physical maximum-row and maximum-column closure;
- volume/background-independent bidirectional Schur coefficient q_phys < 1;
- ordered one-link sweep path loss controlled by six-spatial residual energy;
- genuine link-indexed sweep-stage local profile ell_e;
- direct Schur receiver using that local profile;
- bounded-concrete core preservation under every one-link sweep prefix;
- sharp Haar one-link local coercivity available at every sweep stage;
- bounded-concrete section transport to the actual physical envelope for bounded strongly measurable tests;
- weighted residual-density energy transport;
- exact overlap-coupling RMS transport;
- quadratic likelihood-ratio density-defect control;
- integrated ENNReal and real-L1 quadratic defect;
- centered expectation Cauchy transport with linear influence coefficient;
- normalized real-weight centered RMS transport;
- actual continuous-vacuum physical one-link RMS background-update Harnack;
- automatic bounded-concrete ground-state section wrapper for that RMS theorem.

### Not yet integrated

- a canonical stagewise observable-specific physical profile u_e(F);
- the actual full-envelope one-sided inequality

~~~text
u_t(F) <= ell_t(F) + sum_s K_ts u_s(F);
~~~

- transport of the new RMS stagewise bounds through the complete remote/resolvent part of the physical envelope K;
- a genuine volume-free global profile majorant on the ground-state joint carrier;
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

For the six genuine color projections P_c,

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

Any genuine q < 1 gives the physical transfer-gap lower bound

~~~text
3*(1-q)/8.
~~~

### #4652 — finite commuting-projection tensorization

Provides the abstract finite Hilbert tensorization receiver used by the beta-zero pair-Haar geometry.

**Status: closed as receiver infrastructure.**

---

## 4. Exact beta-zero endpoint — closed

PRs #4653-#4682 establish:

~~~text
ambient transfer = rank one
physical transfer = rank one
vacuum measure = spatial Haar
ground-state joint measure = pair Haar
gap_beta=0 = 1

kappa_0 = 1/6
q_0 = 5/6
gap(0) >= 1/16
gap(0) = 1
~~~

The 1/16 bound is non-optimal and retained only as a consistency receipt for the six-spatial route.

PR #4675 remains **closed / unmerged / superseded by #4676**.

**Status: closed.**

---

## 5. Positive-beta bidirectional Schur L2 — closed

PRs #4683-#4687 close the matrix side.

The actual physical envelope K has volume/background-independent row and column control by

~~~text
q_phys(s,beta)
  = 18 * eta(beta) + rho_osc(s,beta)
~~~

on the canonical strict interval, with

~~~text
0 <= q_phys < 1.
~~~

Therefore

~~~text
sum_t (sum_s K_ts v_s)^2
  <= q_phys^2 * sum_s v_s^2.
~~~

And for nonnegative u, ell satisfying

~~~text
u_t <= ell_t + sum_s K_ts u_s,
~~~

Lean proves

~~~text
(1-q_phys)^2 * sum_t u_t^2
  <= sum_t ell_t^2.
~~~

**Status: matrix / Schur / resolvent side closed.**

Do not re-prove this layer.

---

## 6. Sweep local-energy bridge — closed

### #4688 — generic nested-block theorem

For a real Hilbert space, if a block projection B absorbs every projection P_c in an ordered sweep,

~~~text
B(P_c x) = Bx,
~~~

then no pairwise commutativity is required to prove

~~~text
PathLoss(P,cs,x) <= ||x-Bx||^2.
~~~

### #4689 — genuine six-spatial specialization

~~~text
PathLoss_c(f) <= ||f-P_c f||^2

(1/6) * sum_c PathLoss_c(f)
  <= E_6sp(f).
~~~

### #4690 — link-indexed local profile

Defines the nonnegative sweep-stage amplitude ell_e(f) on genuine spatial links:

~~~text
(1/6) * sum_e ell_e(f)^2
  = SixSpatialOneLinkSweepPathLoss(f)
  <= E_6sp(f).
~~~

No volume-dependent color-class multiplicity appears.

**Status: closed.**

---

## 7. Concrete Schur receiver — closed

PR #4691 feeds the #4690 local profile into #4687.

For every nonnegative u satisfying

~~~text
u_t <= ell_t(f) + sum_s K_ts u_s,
~~~

Lean proves

~~~text
(1/6) * (1-q_phys)^2 * sum_e u_e^2
  <= E_6sp(f).
~~~

A relative-Poincare wrapper exposes the only further premise:

~~~text
||f-center(f)||^2 <= sum_e u_e^2.
~~~

This theorem does **not** assert existence of u.

**Status: receiver closed; observable-specific premises remain open.**

---

## 8. Bounded-concrete sweep invariance — closed

PR #4692 proves:

~~~text
f in boundedConcreteCore
  -> one-link condExpL2(f) in boundedConcreteCore
  -> every finite same-color sweep stays in boundedConcreteCore
  -> every canonical sweep prefix stays in boundedConcreteCore.
~~~

The proof uses ordinary conditional expectation only to construct a measurable representative and identifies the resulting L2 class through MemLp.condExpL2_ae_eq_condExp.

No arbitrary L2 quotient representative is evaluated pointwise.

**Status: closed.**

---

## 9. Stagewise sharp Haar local coercivity — closed

PR #4693 combines #4692 with the existing sharp bounded-core one-link theorem.

For bounded-concrete input, any sweep prefix cs, and next link e, the stage vector x_cs has an explicit bounded strongly measurable representative F_cs satisfying

~~~text
SharpHaarVarianceFunctional(F_cs,e)
  <= ENNReal.ofReal (||x_cs - P_e x_cs||^2).
~~~

The exact exp(-16 beta) coefficient remains encoded in the existing sharp Haar functional.

The canonical Finset.univ.toList.take k prefix form is packaged explicitly.

**Status: closed.**

---

## 10. #4695 — bounded-concrete sections reach the actual physical envelope

PR #4695 connects the current concrete ground-state section type to the already-canonical physical one-link influence envelope.

For bounded strongly measurable tests, actual source-value updates of the literal normalized one-link laws satisfy the existing physical envelope bound.

The centered-radius wrapper proves schematically

~~~text
|E_u phi - E_v phi|
  <= K_target,source * radius
~~~

when

~~~text
|phi-center| <= radius.
~~~

This is an actual-K theorem and requires no continuity hypothesis on phi.

However, it is a sup-radius statement, not yet the desired RMS recurrence.

**Status: closed as an actual-K bounded-test/type bridge.**

---

## 11. #4696-#4697 — weighted residual and exact overlap RMS energy — closed

### #4696

Mutual likelihood-ratio domination controls the sum of the left/right residual densities:

~~~text
(p-min(p,q)) + (q-min(p,q)) = |p-q|.
~~~

This is upgraded to arbitrary nonnegative weighted lower integrals.

The intended weight

~~~text
ofReal ((X-c)^2)
~~~

is packaged directly.

### #4697

The exact one-link overlap coupling is decomposed into:

~~~text
diagonal branch + residual-product branch.
~~~

The diagonal branch contributes zero centered difference energy.

The residual-product branch is controlled by the centered-square residual marginals, and #4696 converts those into the same likelihood-ratio influence coefficient times the two full conditional centered energies.

**Status: generic exact overlap RMS transport closed.**

---

## 12. #4698-#4701 — quadratic likelihood-ratio / Cauchy spine — closed

### #4698 — pointwise quadratic defect

Under mutual K-domination,

~~~text
(p-q)^2 / (p+q)
  <= c(K)^2 * (p+q).
~~~

A full-L1-normalized version is also packaged.

### #4699 — ENNReal integration

For normalized densities,

~~~text
integral ((p-q)^2/(p+q))
  <= (2*c(K))^2
~~~

in ENNReal lower-integral form.

### #4700 — real-L1 promotion

The quadratic defect is promoted to an ordinary real Integrable function and real integral inequality.

### #4701 — centered expectation Cauchy

Pinned mathlib Hölder/Cauchy is used to prove

~~~text
| integral (X-c)*(p-q) |
  <= (2*c(K)) *
     sqrt(integral (X-c)^2*(p+q)).
~~~

After the L2 square root, the influence coefficient remains linear.

This linearity is the key reason the theorem is compatible with a profile recurrence of the form K*u.

**Status: closed.**

---

## 13. #4702 — normalized real-weight RMS transport — closed

For nonnegative real weights w,v with positive masses and mutual pointwise comparison

~~~text
w <= R*v
v <= R*w
R >= 1,
~~~

normalization costs one further factor R, giving an R^2 likelihood-ratio comparison.

Lean proves

~~~text
|E_w[X-c] - E_v[X-c]|
  <= 2*c(R^2) *
     sqrt(E_w[(X-c)^2] + E_v[(X-c)^2]).
~~~

**Status: closed.**

---

## 14. #4703 — actual physical one-link RMS background transport — closed

PR #4703 specializes #4702 to the literal continuous-vacuum physical one-link fiber law under a distinct background-link update.

The raw reference weights are mutually exp(32*beta)-comparable. After normalization the final coefficient is exactly the already-defined

~~~text
BackgroundUpdateHarnackInfluence(beta).
~~~

The theorem has the form

~~~text
|E_u[X-c] - E_v[X-c]|
  <= BackgroundUpdateHarnackInfluence(beta)
     * sqrt(E_u[(X-c)^2] + E_v[(X-c)^2]).
~~~

No new influence coefficient is introduced.

**Status: closed for local physical background updates.**

Important boundary: this coefficient is the background-update Harnack coefficient, not yet the complete full physical envelope K including remote/resolvent propagation.

---

## 15. #4704 — bounded-concrete physical RMS wrapper — closed

PR #4704 removes the explicit first- and second-moment hypotheses from #4703 for bounded strongly measurable concrete ground-state sections.

Given

~~~text
||F(z)|| <= bound,
~~~

every one-link concrete section X is bounded and strongly measurable.

The existing one-link fiber-weight integrability then automatically yields integrability of

~~~text
weight * (X-c)
weight * (X-c)^2.
~~~

Therefore the #4703 physical RMS theorem applies directly to bounded-concrete ground-state sections.

This is exactly the type of representative returned by #4693 at every canonical sweep stage.

No arbitrary joint-L2 quotient representative is evaluated pointwise.

**Status: closed.**

---

## 16. Active theorem frontier — stagewise bounded-concrete physical RMS hybrid profile assembly

This is now the immediate mathematical frontier.

### Inputs already closed

- #4687 — full actual physical envelope K and q_phys < 1;
- #4690 — genuine link-indexed local profile ell_e;
- #4691 — one-sided profile -> Schur/Poincare receiver;
- #4692 — bounded-concrete sweep-prefix invariance;
- #4693 — explicit bounded stage representative + sharp Haar residual;
- #4695 — actual-K bounded/centered-radius section transport;
- #4696-#4702 — generic RMS likelihood-ratio/Cauchy spine;
- #4703 — local actual physical RMS background-update theorem;
- #4704 — automatic bounded-concrete section wrapper;
- #852-#906 — canonical hybrid, target trajectory, endpoint coupling, covariance/variance machinery.

### Immediate goal

For every bounded-concrete input and every canonical sweep stage, use the #4693 representative in #4704 and transport the resulting RMS amplitudes through the existing hybrid/trajectory machinery.

Package a nonnegative spatial-link profile

~~~text
u_e(F)
~~~

and prove

~~~text
u_t(F)
  <= ell_t(F)
     + sum_s K_ts u_s(F).
~~~

### Main unresolved point

#4704 gives local physical RMS control with the background-update Harnack coefficient.

The final recurrence must use the **actual full physical envelope K from #4687**, whose remote part is generated by covariance decay / resolvent transport.

Therefore the next proof must connect the stagewise RMS quantities to the existing local-plus-remote physical envelope architecture. It must not replace K by a new coarser ad hoc coefficient.

### Acceptance criterion

The theorem should use:

- actual ground-state / physical conditional-law objects;
- bounded-concrete stage representatives from #4693;
- actual full physical envelope K;
- no volume-dependent coefficient;
- no hidden same-color independence or interacting commutativity;
- no sup-norm substitute for the required RMS/L2 statement.

**Status: open.**

---

## 17. Second active theorem — genuine global profile majorant

After u_e(F) and the one-sided recurrence exist, prove

~~~text
||F-center(F)||_L2^2
  <= sum_e u_e(F)^2
~~~

or an equivalent independent-pair energy inequality on the correct ground-state joint carrier.

### Existing input

The raw Wilson hybrid profile already has a finite global pair majorant.

### Main danger

The naive finite hybrid telescoping estimate carries an edge-cardinality Cauchy factor. Reusing it directly would reintroduce volume dependence.

The positive-beta ground-state theorem must instead exploit the current stagewise/local RMS structure.

**Status: open.**

---

## 18. Positive-beta bounded-core Poincare target

Once Sections 16 and 17 are closed, #4691 gives

~~~text
global centered energy
  <= sum_e u_e^2
  <= (1-q_phys)^(-2) * sum_e ell_e^2
  <= 6 * (1-q_phys)^(-2) * E_6sp.
~~~

Equivalently,

~~~text
positive coefficient * ||F-center(F)||^2
  <= E_6sp(F).
~~~

Do not freeze the final coefficient until the actual u-profile normalization, sharp Haar factor, and global majorant are connected.

**Status: open, abstract receiver ready.**

---

## 19. Full genuine joint L2 and physical transfer gap

After a bounded-core positive-beta Poincare theorem:

1. apply #4650 to extend to full genuine joint L2;
2. use #4651 to obtain six-spatial Rayleigh q(beta) < 1;
3. feed the physical transfer-gap receiver;
4. obtain a finite-volume gap lower bound independent of volume on the selected positive-beta interval;
5. transport to the exact Hamiltonian normalization and vacuum-orthogonal sector.

This remains a lattice theorem, not yet the continuum mass gap.

---

## 20. Thermodynamic / infinite-volume physical construction

After a uniform finite-volume physical gap:

1. formalize compatible finite-volume embeddings/restrictions;
2. prove consistency of vacuum states and observables;
3. establish the chosen compactness/projective/direct-limit mechanism;
4. construct the infinite-volume Euclidean physical state;
5. preserve reflection positivity, gauge invariance, clustering, and nontrivial observable content.

**Status: downstream.**

---

## 21. Continuum OS / Wightman construction

Required downstream units include:

- continuum Euclidean invariance;
- reflection positivity;
- regularity sufficient for OS reconstruction;
- decay/clustering compatible with spectral interpretation;
- nontrivial physical Hilbert space and observable algebra;
- Wightman/OS reconstruction on the same-root theory.

**Status: downstream.**

---

## 22. Continuum mass gap

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

The finite-volume gap must survive every limiting and identification step actually used.

A fixed-volume eigenvalue, an auxiliary transfer matrix, or an unrelated continuum limit is insufficient.

**Status: downstream / not yet proved.**

---

## 23. Recent canonical theorem units

| PR | Status | Role | Merge commit |
| --- | --- | --- | --- |
| #4690 | merged | link-indexed sweep-stage local profile | 199507d12c903539aad9265f2b6969fb2fca375c |
| #4691 | merged | local profile -> uniform Schur receiver | c99af54a38a0338cee680817d806745a055031f6 |
| #4692 | merged | bounded-concrete sweep invariance | 911c5246f134e1ac4819e496c3bea2f2b288094c |
| #4693 | merged | stagewise sharp Haar local coercivity | 73d90bb97eb1a906d1d11eec10314e1ce1feb518 |
| #4695 | merged | bounded-concrete section -> actual physical influence envelope | 4a573e91d4600e7288b0df6e0a9498223b74c04a |
| #4696 | merged | weighted residual energy by sharp influence | fe7b2a445d2f5ea2b77ee37978c5e51f8f28fbf1 |
| #4697 | merged | exact overlap coupling -> RMS influence energy | 0726c1a19b205374f82186d3ae751687dfc0aa57 |
| #4698 | merged | quadratic likelihood-ratio influence bound | 6fc5ec72c2f91f25f966938151d1a93fcf995acf |
| #4699 | merged | integrated quadratic likelihood-ratio defect | 3e8d4134a5b556f009c96952de91537787cdde1f |
| #4700 | merged | promote quadratic defect to real L1 | 530312e734e2755650c9a97ad8237c47c94dc1ce |
| #4701 | merged | centered expectation Cauchy from quadratic influence | 4ec500197478989987305c8773d729e3b0197888 |
| #4702 | merged | normalized real-weight centered RMS transport | 3f92826baadbd9f7db2b28333ff2e0653c368fb5 |
| #4703 | merged | actual physical one-link centered RMS Harnack | e9a0c73aec92865b0841bc912089cf001cb568ef |
| #4704 | merged | bounded-concrete physical RMS Harnack wrapper | f22fbd1db7325dfe2da08e90b278b3bd14976b89 |
| #4675 | closed / unmerged | superseded by #4676 | — |

Recent exact-head validation:

- #4698: 9b019ce1d0ae071b8ae7b4596daa8acde4a3181f — Fast Check #14922 / run 35952342805: success.
- #4699: 1134d996a8e01b0035e576ebe489a374d76185c1 — Fast Check #14925 / run 35953532356: success.
- #4700: c5108d8f6fc0f189f09d0b90055d64d23d62f585 — Fast Check #14928 / run 35954459754: success.
- #4701: 7570aef3cc221c66d77c094ae1ee2bbd30c86af8 — Fast Check #14931 / run 35955246261: success.
- #4702: e383e7252935af64dcdb4d21cbf624b541ceb6a6 — Fast Check #14934 / run 35958592059: success.
- #4703: 690518df93d0654284f3e674f7222332e8372239 — Fast Check #14943 / run 35962807067: success.
- #4704: aa6a32a597d0920bc1a4305f4c6c63357b6bee76 — Fast Check #14946 / run 35972259556: success.

Current theorem-bearing baseline before this docs refresh:

**f22fbd1db7325dfe2da08e90b278b3bd14976b89**

---

## 24. Lean 4 / mathlib engineering rules

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Operational rules:

1. inspect the whole changed module, CompileSmoke, import graph, and dependent API when CI fails;
2. do not infer mathematical failure from a single elaboration message before checking exact types and imports;
3. treat the pinned mathlib revision as authority rather than current master;
4. keep dependent Lp measure transport narrow;
5. distinguish retained and ambient measurable spaces explicitly in conditional-expectation proofs;
6. remember that local MeasurableSpace definitions can participate in typeclass inference; restore the intended ambient instance explicitly when necessary;
7. use ordinary condExp representatives only through measurable/a.e. identities; do not pointwise evaluate arbitrary L2 quotient representatives;
8. use MemLp.condExpL2_ae_eq_condExp for the L2/ordinary conditional-expectation bridge;
9. use typed simpa using for dependent reindexing when rw does not syntactically match;
10. normalize finite color indices to Fin 6 early when required by receivers;
11. prefer forward ENNReal/ofReal rewrites with explicit intermediate normal forms over coercion-sensitive reverse rw;
12. when Integrable.add produces Pi-valued pointwise addition, expose Pi.add_apply before ring-style algebra;
13. for a+c <= b+d, prefer explicit add_le_add if add_le_add_left/right inference is ambiguous;
14. remember that rw or calc may finish a goal; do not append unconditional tactics after a closed goal;
15. validate exact PR head, workflow completion, and exact-head commit-status receipt before merge;
16. after docs-only merges, separate current branch pointer from the last theorem-bearing merge.

---

## 25. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe formal/real-hilbert-uniform-coercive-strong-limit;
2. expected theorem-bearing baseline is f22fbd1db7325dfe2da08e90b278b3bd14976b89 unless a later theorem merge has occurred;
3. if a docs-only merge follows this refresh, keep the theorem baseline distinct from the current pointer;
4. retain #4687 as the uniform full physical K / Schur authority;
5. retain #4690 as the link-indexed local-profile ell_e authority;
6. retain #4691 as the concrete Schur/Poincare receiver;
7. retain #4692 as bounded-concrete sweep-invariance authority;
8. retain #4693 as stagewise bounded representative + sharp Haar authority;
9. retain #4695 as the actual-K bounded/centered-radius concrete-section bridge;
10. retain #4696-#4702 as the generic RMS likelihood-ratio/Cauchy spine;
11. retain #4703 as local physical one-link RMS background-update authority;
12. retain #4704 as the bounded-concrete automatic-moment RMS wrapper;
13. reuse #852-#906 rather than rebuilding hybrid/trajectory probability geometry;
14. feed the #4693 canonical stage representatives into #4704;
15. package the resulting RMS amplitudes into the actual u_e(F);
16. connect those amplitudes to the full physical envelope K, including its remote/resolvent contribution;
17. prove u_t <= ell_t + sum_s K_ts u_s;
18. then prove the global profile majorant without a volume factor;
19. feed the result through #4691 -> #4650 -> #4651 toward a positive-beta volume-independent physical gap.

The immediate theorem unit is:

**Stagewise bounded-concrete physical RMS hybrid profile assembly.**
