# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-23 JST

Repository: **itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

The theorem-bearing baseline immediately before this documentation refresh is:

**1071479971e78354deae2d7904dc8f6d2fe8a5b0**

This is the merge commit of PR #4668, **Prove shared-base product conditional expectation collapse**.

The default branch **main** is not theorem authority.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean artifacts;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A docs-only merge may advance a branch pointer without changing the theorem-bearing mathematical baseline.

---

## 0. Claim boundary

The repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

Integrated at this checkpoint:

- finite-volume periodic Wilson / OS / physical-transfer construction;
- canonical nonnegative vacuum and ground-state transform;
- high-temperature physical response, influence, covariance, and strict full-sweep contraction;
- genuine six-spatial L2 residual / Rayleigh receivers;
- abstract finite tensorization for commuting Hilbert projections;
- exact beta-zero ambient and physical rank-one transfer;
- exact beta-zero vacuum measure = spatial Haar;
- exact beta-zero ground-state joint measure = pair Haar;
- exact beta-zero top-orthogonal normalized transfer = 0;
- exact finite-volume beta-zero physical transfer gap = 1;
- literal pair-Haar six-spatial color projections;
- exact color/off-color Haar splitting;
- six-retained common-fixed boundary-L2 identification;
- idempotence and symmetry of the six beta-zero projections;
- generic product-probability conditional-expectation fiber formula;
- generic Hilbert range-invariance -> commutation theorem;
- generic three-factor shared-base conditional-expectation collapse.

Not yet integrated:

- the Wilson-specific range-invariance theorem for every pair of beta-zero spatial colors;
- pairwise commutation of the genuine beta-zero six-spatial projection family;
- an explicit beta-zero six-spatial frame/Rayleigh constant on the required centered physical sector;
- a volume-uniform positive-beta genuine ground-state L2 frame / Rayleigh coefficient;
- the resulting scale-independent positive-beta physical transfer/Hamiltonian gap;
- the thermodynamic/infinite-volume physical construction;
- the continuum OS/Wightman Yang--Mills construction;
- the final continuum mass-gap theorem.

---

## 1. Finite-volume Wilson / OS / physical-transfer foundation — closed as infrastructure

The repository already contains:

~~~text
periodic Wilson action / one-slab kernel
  -> Haar L2 carriers
  -> OS reflection-positive boundary construction
  -> Gauss-law physical restriction
  -> compact positive physical transfer
  -> top eigenspace / canonical nonnegative vacuum
  -> ground-state transform
  -> vacuum and joint probability laws
  -> genuine one-link and color conditional expectations
~~~

The current work does not restart this foundation.

---

## 2. Canonical high-temperature response and physical contraction — closed

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

For fixed s > 1:

~~~text
spatial decay ratio = s^(-1) < 1
~~~

The oscillation sharpening vanishes at beta = 0, and #4648 produces a positive interval on which the physical sweep coefficient is strictly below one uniformly in finite volume.

**Status: closed.**

---

## 3. Genuine ground-state L2 receiver — closed as infrastructure

### #4650: bounded-core closure

Integrated:

- six-spatial normalized residual energy on the genuine ground-state joint L2 carrier;
- continuity of the residual energy;
- dense bounded concrete core;
- coefficient-preserving extension to the full joint L2 carrier.

### #4651: six-spatial random-scan receiver

For the six genuine conditional-expectation projections P_c:

~~~text
P_rs = (1/6) * sum_c P_c
inner(P_rs x, x) = (1/6) * sum_c ||P_c x||^2
~~~

The frame inequality

~~~text
kappa * ||x||^2 <= (1/6) * sum_c ||x - P_c x||^2
~~~

is equivalent to

~~~text
inner(P_rs x, x) <= (1-kappa) * ||x||^2.
~~~

Any genuine q < 1 yields the physical transfer-gap lower bound

~~~text
3*(1-q)/8.
~~~

**Status: receiver closed; quantitative model premise still open.**

---

## 4. Abstract commuting-projection tensorization — closed

PR #4652 proves for a finite pairwise commuting family of self-adjoint idempotents:

~~~text
||x - P_sweep x||^2 <= sum_c ||x - P_c x||^2.
~~~

Integrated ingredients include:

1. norm contraction;
2. commutation through finite sweeps;
3. monotonicity of coordinate defects;
4. one-step Pythagorean decomposition;
5. finite-list tensorization;
6. Fintype full-sweep tensorization.

**Status: closed.**

---

## 5. Exact beta-zero Wilson endpoint — closed

### #4653: ambient transfer

At beta = 0:

~~~text
K_0(A,B) = 1
T_0 = |1_Haar><1_Haar|.
~~~

### #4654: physical transfer

The ambient identity descends to the actual Gauss-law physical carrier:

~~~text
T_phys,0 = |1_phys><1_phys|
||T_phys,0|| = 1.
~~~

### #4655: canonical nonnegative vacuum

The selected normalized nonnegative top vector is exactly the physical constant-one unit vector.

### #4656: exact probability laws

Exactly:

~~~text
vacuum_measure(beta=0) = spatial_Haar_measure
ground_state_joint_measure(beta=0) = pair_Haar_measure.
~~~

### #4657: exact beta-zero transfer gap

The normalized physical transfer annihilates the full top-orthogonal sector:

~~~text
R_0 = 0
||R_0|| = 0
physical_transfer_gap(beta=0) = 1.
~~~

The value one is exact and independent of finite volume.

**Status: closed.**

---

## 6. Beta-zero six-spatial product-Haar specialization — integrated structure

This is now the active finite-volume theorem lane.

### 6.1 #4662 — literal pair-Haar carrier and color projections

Integrated:

- literal two-slice pair-Haar L2 carrier;
- identification of the beta-zero ground-state joint L2 type with that literal carrier;
- one-color conditional-expectation projection;
- Fin 6 family of six spatial-color projections.

### 6.2 #4663 — color/off-color Haar splitting

For each spatial color, the right boundary is split into

~~~text
selected color block × off-color block
~~~

by Mathlib's finite-product measurable equivalence, with exact measure-preserving product-Haar transport.

The beta-zero ground-state joint law is therefore represented in coordinates of the form

~~~text
(left boundary × off-color right boundary) × selected color block.
~~~

### 6.3 #4664 — common-fixed range geometry

Integrated:

~~~text
intersection of six right-retained L2 ranges
  = complete left-boundary L2 subspace

intersection of six left-retained L2 ranges
  = complete right-boundary L2 subspace.
~~~

This is the canonical common-fixed geometry to reuse in tensorization.

### 6.4 #4665 — projection geometry

Each literal pair-Haar spatial-color projection is proved:

- idempotent;
- symmetric/self-adjoint.

The properties are packaged for the Fin 6 family.

### 6.5 #4666 — product-probability fiber conditional expectation

For a product probability measure μ.prod ν:

- the conditional law of the second coordinate given the first is the constant kernel ν;
- conditional expectation onto the first-coordinate sigma-algebra is literal integration over the second factor.

This is the generic Fubini engine for the color projections.

### 6.6 #4667 — Hilbert range-invariance receiver

For a symmetric operator P and a symmetric idempotent Q:

~~~text
P(range Q) subset range Q
    =>
P Q = Q P.
~~~

The proof uses:

~~~text
range Q invariant
  -> by symmetry of P, (range Q)^perp invariant
  -> by symmetry of Q, (range Q)^perp = ker Q
  -> range Q and ker Q are P-invariant
  -> LinearMap.IsIdempotentElem.commute_iff
  -> commutation.
~~~

The family theorem packages this for finite projection tensorization.

### 6.7 #4668 — shared-base three-factor collapse

On

~~~text
((gamma × alpha) × beta, (rho.prod mu).prod nu),
~~~

a right-retained function depending only on (gamma,beta), when conditionally averaged onto the left-retained information (gamma,alpha), collapses to a function of the common base gamma alone.

Equivalently, the cross conditional expectation lands in the common-base measurable subspace.

This is the generic measure-theoretic input needed to prove color-projection range invariance.

**Status through #4668: integrated.**

---

## 7. Immediate frontier — Wilson-specific pairwise range invariance and commutation

The next theorem should instantiate the generic #4668 collapse on the actual finite Wilson pair-Haar color coordinates.

For all beta-zero spatial colors c,d, prove:

~~~text
P_c (range P_d) subset range P_d.
~~~

### Intended proof route

1. start on the literal beta-zero pair-Haar carrier from #4662;
2. use #4663 and the retained-coordinate measurable equivalences to isolate:
   - the coordinates retained by d;
   - the coordinates averaged by c;
   - their common retained base;
3. reindex to a three-factor product;
4. apply #4668 to show the cross conditional expectation depends only on the common base;
5. transport the resulting measurability statement back to the actual d-retained sigma-algebra;
6. conclude P_c(range P_d) subset range P_d;
7. invoke #4667;
8. obtain for every c,d:

~~~text
P_c P_d = P_d P_c.
~~~

### Important boundary

Do **not** claim positive-beta commutativity. The present product-Haar argument is a beta-zero statement.

### Acceptance criterion

A theorem on the literal/genuine beta-zero joint L2 carrier proving pairwise commutation of the six actual spatial-color conditional-expectation projections, with no new probabilistic or Poincare assumption.

---

## 8. Beta-zero six-spatial frame / Rayleigh theorem

After pairwise commutation is available:

1. feed the six actual projections into #4652;
2. obtain
   ~~~text
   ||x - P_sweep x||^2 <= sum_c ||x - P_c x||^2;
   ~~~
3. identify the common-fixed/sweep component using #4664, not a new centering object;
4. restrict to the required centered/right-boundary physical sector;
5. derive an explicit beta-zero frame coefficient kappa0 > 0;
6. convert through #4651 to q0 < 1:
   ~~~text
   inner(P_rs x, x) <= q0 * ||x||^2;
   ~~~
7. check compatibility with the independent exact transfer endpoint #4657.

The documentation intentionally does **not** pre-commit to a numerical kappa0 or q0. The formal proof should determine the constant.

### Acceptance criterion

An explicit positive beta-zero frame/Rayleigh constant on the actual physical centered sector, without adding a new unproved Poincare hypothesis.

---

## 9. Positive-beta / high-temperature L2 bridge

This remains the central finite-volume quantitative theorem after beta-zero tensorization closes.

Available inputs:

1. exact one-link ground-state conditional laws;
2. one-link conditional variance/residual identities;
3. physical influence and response estimates;
4. strict volume-independent physical sweep contraction (#4648);
5. exact beta-zero pair-Haar law (#4656);
6. exact beta-zero physical transfer gap = 1 (#4657);
7. bounded-core closure (#4650);
8. genuine Rayleigh receiver (#4651);
9. beta-zero product-Haar commutation infrastructure (#4662-#4668).

Missing theorem:

~~~text
physical interdependence coefficient < 1
    =>
genuine ground-state L2 Rayleigh coefficient < 1
~~~

with a coefficient independent of finite volume.

A continuous-state Dobrushin / approximate-tensorization theorem is a plausible presentation, but it must be proved for the actual ground-state conditional laws and preserve the repository's target/source orientation.

### Required distinction

Bounded-test / total-variation-style influence contraction is not the same theorem as L2 Poincare/Rayleigh coercivity.

### Acceptance criterion

Produce q < 1, independent of finite volume in the selected high-temperature scaling family, such that

~~~text
inner(P_rs x, x) <= q * ||x||^2
~~~

on the selected physical top-orthogonal sector.

Then #4651 gives

~~~text
uniform physical transfer-gap lower bound = 3*(1-q)/8 > 0.
~~~

---

## 10. Uniform finite-volume Hamiltonian gap

Once a scale-independent q < 1 is available:

1. apply the physical transfer-gap receiver;
2. obtain a positive volume-independent transfer gap;
3. transport it to the exact Hamiltonian normalization;
4. prove vacuum-orthogonal coercivity;
5. keep all statements on the same-root physical Wilson/OS carrier.

### Acceptance criterion

There exists gamma > 0 independent of finite volume such that every member of the selected scaling family has excitation gap at least gamma.

This is still a lattice theorem, not the continuum mass gap.

---

## 11. Thermodynamic / infinite-volume physical construction

After a uniform finite-volume gap:

1. formalize compatible finite-volume embeddings/restrictions;
2. prove consistency of vacuum states and observables;
3. establish the chosen compactness/projective/direct-limit mechanism;
4. construct the infinite-volume Euclidean physical state;
5. transport reflection positivity, gauge invariance, clustering, and nontrivial observable content.

The limiting theory must remain the same-root Wilson/OS construction.

---

## 12. Continuum OS / Wightman construction

Required downstream units include:

- continuum Euclidean invariance;
- reflection positivity;
- regularity for OS reconstruction;
- cluster/decay estimates compatible with the spectral interpretation;
- nontriviality of the physical Hilbert space and observable algebra;
- Wightman/OS reconstruction on the same physical theory.

Only after these are established can the continuum Hamiltonian be identified with the target Yang--Mills theory.

---

## 13. Continuum mass gap

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive spectral lower edge on the vacuum-orthogonal sector.

The finite-volume constant must survive every limiting and identification step actually used.

A fixed-volume eigenvalue, an auxiliary transfer matrix, or an unrelated continuum limit is not sufficient.

---

## 14. Lean 4 / mathlib engineering rules

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Operational rules:

1. inspect the whole changed file, CompileSmoke, import graph, and dependent API when CI fails;
2. do not infer mathematical failure from an elaboration failure;
3. treat the pinned Mathlib revision as authority rather than current master;
4. verify a module path exists at the pin before adding it as an import;
5. verify theorem namespaces at the pin before using field notation;
6. remember that IsIdempotentElem may reduce to an equality, so namespace theorems may require a fully-qualified call;
7. keep ContinuousLinearMap / LinearMap coercion boundaries explicit;
8. use theorem-level rewrites before change when equality is not definitional;
9. at Lp/a.e. boundaries, prefer explicit representative lemmas and calc chains;
10. avoid reverse rewriting through unconstrained implicit measure arguments;
11. reduce large operator equalities pointwise when possible;
12. keep local SU(N) topology/measurability instances narrowly scoped;
13. raise heartbeat/recursion limits only after signature, orientation, instance, and definitional-equality checks;
14. validate the exact PR head, then confirm the MCP completion receipt before merging;
15. after any parallel PR merge, re-observe neighboring open PRs because their base/mergeability may have changed.

---

## 15. Recent canonical theorem units

| PR | Status | Role |
| --- | --- | --- |
| #4648 | merged | strict positive high-temperature physical sweep gate |
| #4650 | merged | six-spatial bounded-core L2 closure |
| #4651 | merged | genuine six-spatial random-scan Rayleigh receiver |
| #4652 | merged | finite tensorization for commuting Hilbert projections |
| #4653 | merged | beta-zero ambient transfer rank one |
| #4654 | merged | beta-zero physical transfer rank one |
| #4655 | merged | beta-zero canonical nonnegative vacuum = constant one |
| #4656 | merged | beta-zero vacuum/joint laws = Haar/pair Haar |
| #4657 | merged | exact beta-zero physical transfer gap = 1 |
| #4662 | merged | literal pair-Haar carrier and six spatial projections |
| #4663 | merged | beta-zero six-spatial Haar color split |
| #4664 | merged | six-retained intersections = boundary L2 |
| #4665 | merged | beta-zero six-spatial projection idempotence/symmetry |
| #4666 | merged | product-probability conditional-expectation fiber formula |
| #4667 | merged | range invariance -> Hilbert projection commutation |
| #4668 | merged | shared-base product conditional-expectation collapse |

The theorem-bearing baseline immediately before this docs refresh is:

**1071479971e78354deae2d7904dc8f6d2fe8a5b0**

Recent exact-head receipts:

- #4666: 04e79a500a4a33b92ab4f6021aaf650e34ab94d7 — Fast Check #14810 / run 35819293208: success.
- #4667: 174886cec0e2c79864dffaf988e597f2d29cb7de — Fast Check #14815 / run 35821420342: success.
- #4668 synchronized head: 5d2c0010e11c8e40d8836443e7d168b7d520d4be — Fast Check #14817 / run 35822417043: success.

---

## 16. Short restart instruction

At the start of the next theorem thread:

1. fresh re-observe formal/real-hilbert-uniform-coercive-strong-limit;
2. do not use main as theorem authority;
3. distinguish docs-only pointer advances from theorem-bearing merges;
4. retain #4657 as the closed exact beta-zero gap endpoint;
5. retain #4662-#4668 as the integrated beta-zero product-Haar commutation infrastructure;
6. prove the Wilson-specific pairwise range-invariance theorem;
7. feed it to #4667 to obtain six-color pairwise commutation;
8. apply #4652 and the #4664 common-fixed identification;
9. derive the beta-zero six-spatial frame/Rayleigh constant;
10. then construct the volume-uniform positive-beta L2 bridge.
