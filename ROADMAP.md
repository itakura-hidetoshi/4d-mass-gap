# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-23 JST

Repository: **itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline before this documentation refresh:

**bbd064ddff7814a804c2ba319e6c365dabd9ecb4**

This is the merge commit of PR #4678 and contains the immediately preceding merged PR #4677.

The default branch **main** is not theorem authority.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts;
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
- exact beta-zero normalized physical transfer = 0 on the top-orthogonal sector;
- exact finite-volume beta-zero physical transfer gap = 1;
- complete literal pair-Haar six-spatial projection geometry;
- actual Wilson-specific range invariance and pairwise commutation;
- actual beta-zero full-sweep tensorization;
- full-sweep fixed sector = complete fst-boundary L2;
- exact literal beta-zero frame coefficient kappa_0 = 1/6;
- exact literal beta-zero random-scan Rayleigh factor q_0 = 5/6;
- direct physical-top-orthogonal -> pair-Haar fst-orthogonal bridge;
- complementary beta-zero Doob/coarse-projection zero bridge.

Not yet integrated:

- a packaged genuine physical beta-zero six-spatial kappa_0=1/6 / q_0=5/6 theorem;
- the resulting six-spatial receiver consistency bound 1/16 on the physical beta-zero sector;
- a volume-uniform positive-beta genuine ground-state L2 frame/Rayleigh coefficient;
- the resulting scale-independent positive-beta physical transfer/Hamiltonian gap;
- thermodynamic/infinite-volume physical construction;
- continuum OS/Wightman Yang--Mills construction;
- final continuum mass-gap theorem.

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

For fixed s > 1, the spatial decay ratio is strictly below one. #4648 produces a positive interval on which the physical sweep coefficient is strictly below one uniformly in finite volume.

**Status: closed as the bounded-test / physical-influence side of the later L2 bridge.**

---

## 3. Genuine ground-state L2 receiver — closed as infrastructure

### #4650 — bounded-core closure

Integrated:

- six-spatial normalized residual energy on the genuine ground-state joint L2 carrier;
- continuity of the residual energy;
- dense bounded concrete core;
- coefficient-preserving extension to full L2.

### #4651 — six-spatial random-scan receiver

For the six genuine conditional-expectation projections P_c,

~~~text
P_rs = (1/6) * sum_c P_c
~~~

and

~~~text
kappa * ||x||^2
  <= (1/6) * sum_c ||x - P_c x||^2
~~~

is equivalent to

~~~text
inner(P_rs x, x)
  <= (1-kappa) * ||x||^2.
~~~

Any genuine q < 1 yields the physical transfer-gap lower bound

~~~text
3*(1-q)/8.
~~~

**Status: receiver closed.**

---

## 4. Abstract commuting-projection tensorization — closed

PR #4652 proves for a finite pairwise commuting family of symmetric idempotents:

~~~text
||x - P_sweep x||^2
  <= sum_c ||x - P_c x||^2.
~~~

This theorem is now instantiated by the actual beta-zero six-spatial pair-Haar family.

**Status: closed.**

---

## 5. Exact beta-zero Wilson endpoint — closed

### #4653 — ambient rank one

~~~text
K_0(A,B) = 1
T_0 = |1_Haar><1_Haar|.
~~~

### #4654 — physical rank one

~~~text
T_phys,0 = |1_phys><1_phys|
||T_phys,0|| = 1.
~~~

### #4655 — canonical nonnegative vacuum

The selected canonical nonnegative top vector is exactly the constant physical unit vector.

### #4656 — exact laws

~~~text
vacuum_measure(beta=0) = spatial_Haar
ground_state_joint_measure(beta=0) = pair_Haar.
~~~

### #4657 — exact transfer gap

~~~text
normalized physical transfer on top-orthogonal sector = 0
physical transfer gap(beta=0) = 1.
~~~

The value one is exact and volume-independent at finite volume.

**Status: closed.**

---

## 6. Beta-zero six-spatial pair-Haar projection geometry — closed

### #4662 — literal pair-Haar carrier

- literal pair-Haar joint L2 carrier;
- Fin 6 actual spatial-color conditional-expectation projections.

### #4663 — color/off-color splitting

Selected color and off-color blocks are separated by a measure-preserving product-Haar equivalence.

### #4664 — common-fixed geometry

~~~text
intersection of six right-retained ranges
  = complete fst-boundary L2

intersection of six left-retained ranges
  = complete snd-boundary L2.
~~~

### #4665 — projection geometry

Each actual beta-zero color projection is:

- idempotent;
- symmetric/self-adjoint.

### #4666 — product conditional expectation

Conditional expectation over one factor of a product probability law is literal integration over that factor.

### #4667 — range-invariance receiver

For symmetric P and symmetric idempotent Q:

~~~text
P(range Q) subset range Q
  => P Q = Q P.
~~~

### #4668 — shared-base collapse

On a three-factor product, averaging right-retained data onto left-retained data collapses to the common retained base.

### #4671 — Wilson-specific range invariance

The #4668 shared-base result is transported to actual Wilson coordinates. For all spatial colors c,d:

~~~text
P_c(range P_d) subset range P_d.
~~~

### #4672 — actual pairwise commutation

For all c,d : Fin 6:

~~~text
P_c P_d = P_d P_c.
~~~

### #4673 — full-sweep tensorization

Defines the actual six-spatial full sweep and proves

~~~text
||x - P_sweep x||^2
  <= sum_c ||x - P_c x||^2.
~~~

Also:

~~~text
P_sweep x = x
  <-> for all c, P_c x = x.
~~~

### #4674 — fixed boundary sector

~~~text
P_sweep x = x
  <-> x belongs to complete fst-boundary L2.
~~~

No duplicate centering object is introduced.

### #4676 — exact frame and Rayleigh constants

The actual full sweep is symmetric and idempotent. Therefore on the orthogonal complement of complete fst-boundary L2:

~~~text
P_sweep x = 0.
~~~

Tensorization gives the exact normalized frame coefficient

~~~text
kappa_0 = 1/6.
~~~

The literal pair-Haar random scan

~~~text
P_rs = (1/6) * sum_c P_c
~~~

then satisfies

~~~text
inner(P_rs x, x)
  <= (5/6) * ||x||^2,
~~~

so

~~~text
q_0 = 5/6.
~~~

### #4675 — superseded

PR #4675 is closed and unmerged. It was superseded by #4676 and must not be revived as theorem authority.

**Status: closed.**

---

## 7. Physical beta-zero -> pair-Haar boundary bridge — closed

### #4677 — direct literal-carrier bridge

Defines the literal beta-zero right-boundary pair-Haar L2 isometry and proves:

1. the pullback is snd-coordinate measurable;
2. physical beta-zero top-orthogonality gives zero Haar mean;
3. a snd-measurable mean-zero L2 vector is orthogonal to the complete fst-measurable L2 sector;
4. therefore the physical beta-zero top-orthogonal sector maps into

~~~text
L2(fst-boundary)^perp.
~~~

This is the direct hypothesis needed by #4676.

### #4678 — Doob/coarse-projection bridge

At beta zero:

- vacuum measure = Haar;
- canonical vacuum = one;
- Haar-to-vacuum L2 isometry is onto;
- ambient rank-one transfer annihilation forces the Doob boundary image to vanish;
- therefore the coarse left-boundary projection of the transformed right-boundary lift is zero.

Conceptually:

~~~text
T_0 f = 0
  -> D_0(U_0 f) = 0
  -> Q_0(R_0(U_0 f)) = 0.
~~~

This gives an independent Hilbert/Doob presentation of the same endpoint separation.

**Status: closed.**

---

## 8. Immediate next theorem — package the genuine physical beta-zero six-spatial constants

The geometry is now available; the remaining endpoint work is a short transport/package theorem.

### Goal

For

~~~text
x in physical beta-zero top-orthogonal sector,
~~~

let its beta-zero ground-state/right-boundary image be z.

Use #4677 to prove:

~~~text
z in L2(fst-boundary)^perp.
~~~

Then apply #4676 and transport the norm through the existing isometries.

### Expected exact conclusions

~~~text
(1/6) * ||x||^2
  <= physical six-spatial normalized residual energy at beta=0

inner(P_rs z, z)
  <= (5/6) * ||x||^2.
~~~

Thus the genuine physical endpoint constants are

~~~text
kappa_0 = 1/6
q_0 = 5/6.
~~~

### Consistency receiver

#4651 gives

~~~text
3*(1-q_0)/8
  = 3*(1/6)/8
  = 1/16.
~~~

This is only a six-spatial receiver consistency lower bound. The exact beta-zero physical transfer gap remains the stronger theorem:

~~~text
gap_beta=0 = 1
~~~

from #4657.

### Acceptance criterion

A theorem on the genuine physical beta-zero top-orthogonal sector with no new Poincare hypothesis and no duplicate centering object.

---

## 9. Main finite-volume quantitative frontier — positive-beta volume-uniform L2 bridge

After the endpoint package above, the central missing theorem is:

~~~text
physical interdependence coefficient < 1
    =>
genuine ground-state L2 Rayleigh coefficient < 1
~~~

uniformly in finite volume on a positive high-temperature interval.

Available inputs now include:

1. exact one-link ground-state conditional laws;
2. physical influence and response estimates;
3. strict volume-independent physical sweep contraction (#4648);
4. dense-core/full-L2 closure (#4650);
5. genuine random-scan Rayleigh receiver (#4651);
6. exact beta-zero transfer gap = 1 (#4657);
7. complete beta-zero pair-Haar projection geometry (#4662-#4676);
8. physical beta-zero boundary bridges (#4677-#4678).

### Required distinction

Bounded-test / total-variation-style influence contraction is **not** the same theorem as L2 Poincare/Rayleigh coercivity.

### Acceptance criterion

Produce q(beta) < 1, independent of finite volume in the selected high-temperature family, such that on the selected physical centered sector:

~~~text
inner(P_rs x, x)
  <= q(beta) * ||x||^2.
~~~

Then #4651 gives a positive uniform physical transfer-gap lower bound.

---

## 10. Uniform finite-volume Hamiltonian gap

Once a scale-independent q < 1 is available:

1. apply the physical transfer-gap receiver;
2. obtain a positive volume-independent transfer gap;
3. transport it to the exact Hamiltonian normalization;
4. prove vacuum-orthogonal coercivity;
5. keep all statements on the same-root physical Wilson/OS carrier.

**Acceptance criterion:** a positive lower gap bound independent of finite volume in the selected scaling family.

This is still a lattice theorem, not the continuum mass gap.

---

## 11. Thermodynamic / infinite-volume physical construction

After a uniform finite-volume gap:

1. formalize compatible finite-volume embeddings/restrictions;
2. prove consistency of vacuum states and observables;
3. establish the chosen compactness/projective/direct-limit mechanism;
4. construct the infinite-volume Euclidean physical state;
5. transport reflection positivity, gauge invariance, clustering, and nontrivial observable content.

---

## 12. Continuum OS / Wightman construction

Required downstream units include:

- continuum Euclidean invariance;
- reflection positivity;
- regularity sufficient for OS reconstruction;
- decay/clustering estimates compatible with spectral interpretation;
- nontrivial physical Hilbert space and observable algebra;
- Wightman/OS reconstruction on the same-root theory.

---

## 13. Continuum mass gap

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

The finite-volume bound must survive every limiting and identification step actually used.

A fixed-volume eigenvalue, an auxiliary transfer matrix, or an unrelated continuum limit is not sufficient.

---

## 14. Lean 4 / mathlib engineering rules

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Operational rules:

1. inspect the entire changed file, CompileSmoke, import graph, and dependent API when CI fails;
2. do not infer mathematical failure from direct-elaboration missing-.olean failures;
3. treat the pinned mathlib revision as authority rather than current master;
4. verify theorem namespaces and exact signatures at the pin before coding;
5. keep dependent Lp measure transport narrow; avoid rewriting an entire proof-indexed carrier;
6. for product conditional expectation, pin the ambient product measurable space when implicit metavariables can diverge;
7. prefer literal `Prod.instMeasurableSpace` when definitional identity matters;
8. keep ContinuousLinearMap / LinearMap / LinearIsometry coercion boundaries explicit;
9. use `change` only for definitional equality;
10. remember that `rw` needs an elaborated syntactic occurrence; unfold wrappers first;
11. use `simp only` when global simp would destroy the local representative form;
12. separate structural simplification from arithmetic normalization;
13. use `norm_num` for exact rational identities such as `1 - 6⁻¹ = 5/6`;
14. avoid expensive orthogonal-projection instance synthesis when direct inner-product orthogonality suffices;
15. keep local SU(N) topology/measurability instances narrowly scoped;
16. validate exact PR heads and exact-head MCP completion receipts before merging;
17. after parallel merges, re-observe the theorem-carrier and compare both merge commits against the fresh head.

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
| #4662 | merged | literal pair-Haar carrier and six projections |
| #4663 | merged | color/off-color Haar product split |
| #4664 | merged | common-fixed intersections = boundary L2 |
| #4665 | merged | projection idempotence/symmetry |
| #4666 | merged | product conditional-expectation fiber formula |
| #4667 | merged | range invariance -> commutation receiver |
| #4668 | merged | shared-base product collapse |
| #4671 | merged | Wilson-specific range invariance |
| #4672 | merged | actual six-color pairwise commutation |
| #4673 | merged | actual full-sweep tensorization |
| #4674 | merged | full-sweep fixed sector = fst-boundary L2 |
| #4675 | closed / unmerged | superseded by #4676 |
| #4676 | merged | exact kappa_0=1/6 and q_0=5/6 |
| #4677 | merged | direct physical -> pair-Haar fst-orthogonal bridge |
| #4678 | merged | Doob/coarse-projection beta-zero bridge |

Recent exact-head validation:

- #4676: `ca05fcd095e84d5f3f56b1ae3cb2c4bc56b3ae52` — Fast Check #14843 / run 35843054541: success.
- #4677: `d5da7f0c97f4c736f2e7a41015c003ab1a899a3b` — Fast Check #14856 / run 35850382949: success.
- #4678: `43f73b187073e47b678fd5d9f229646c28d97f27` — Fast Check #14855 / run 35850140311: success.

The theorem-bearing baseline before this docs refresh is:

**bbd064ddff7814a804c2ba319e6c365dabd9ecb4**

---

## 16. Short restart instruction

At the start of the next theorem thread:

1. fresh re-observe `formal/real-hilbert-uniform-coercive-strong-limit`;
2. do not use `main` as theorem authority;
3. keep #4675 closed/unmerged;
4. retain #4676 as the exact literal pair-Haar constants theorem;
5. retain #4677 and #4678 as the closed physical beta-zero boundary bridge;
6. package the genuine physical beta-zero `kappa_0=1/6`, `q_0=5/6` theorem;
7. feed #4651 for the `1/16` consistency lower bound;
8. retain #4657 as the exact endpoint gap `1`;
9. then move to the positive-beta volume-uniform ground-state L2 bridge.
