# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-23 JST

Repository: **itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

The theorem-bearing baseline immediately before this documentation refresh is:

**245d422bef931e769434e2e8607c3d465b9e639b**

This is the merge commit of PR #4656, **Identify exact beta-zero ground-state laws with Haar product laws**.

The default branch main is not theorem authority.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean artifacts;
3. README / ROADMAP;
4. CI receipts;
5. historical summaries or memory.

A docs-only merge may advance a branch pointer without changing the theorem-bearing mathematical baseline.

---

## 0. Claim boundary

The repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

Integrated at the current checkpoint:

- exact finite-volume periodic Wilson / OS / physical-transfer construction;
- canonical vacuum continuation and continuous representatives;
- actual fixed-right response continuity;
- canonical high-temperature half-barrier closure;
- actual physical influence / random-scan contraction;
- spatial covariance clustering;
- terminal covariance decay and cubic-shell summability;
- volume-uniform remote residual;
- positive strict physical full-sweep contraction interval;
- genuine ground-state six-spatial L2 Poincare / Rayleigh receivers;
- abstract commuting-projection tensorization;
- exact beta-zero rank-one ambient and physical transfer;
- exact canonical beta-zero nonnegative vacuum;
- exact beta-zero vacuum measure = Haar;
- exact beta-zero ground-state joint measure = pair Haar.

Open but not yet authoritative:

- PR #4657 — exact beta-zero physical transfer gap = 1.

Not yet integrated:

- a strict volume-uniform genuine ground-state L2 frame / Poincare coefficient for positive beta;
- the resulting scale-independent positive-beta physical transfer/Hamiltonian gap;
- the full thermodynamic/infinite-volume physical construction;
- the continuum OS/Wightman Yang--Mills construction;
- the final continuum mass-gap theorem.

---

## 1. Integrated finite-volume foundation

The existing repository already contains the foundation needed by the current frontier:

~~~text
periodic Wilson action / one-slab kernel
  -> product Haar L2
  -> symmetric Hilbert-Schmidt transfer
  -> Gauss-law physical restriction
  -> compact positive physical transfer
  -> top eigenspace / canonical nonnegative vacuum
  -> ground-state transform
  -> vacuum and joint probability laws
  -> genuine one-link conditional expectations
  -> six-spatial / twelve-spatial finite conditional-expectation families
~~~

This foundation is not being restarted.

---

## 2. Canonical high-temperature response and contraction spine — closed

Integrated chain:

~~~text
#4634 literal fixed-right target-ratio response continuity
#4637 canonical half-barrier closure
#4638 actual weighted physical influence / response decay
#4639 finite influence-path and resolvent propagation
#4640 canonical random-scan variation contraction
#4641 finite covariance resolvent
#4642 spatial random-scan resolvent
#4643 actual spatial covariance clustering
#4644 concrete two-step terminal covariance decay
#4645 cubic-shell summability -> uniform remote residual
#4646 oscillation-sharpened terminal covariance
#4647 beta-zero-vanishing sharpened remote residual
#4648 strict positive high-temperature physical sweep gate
~~~

For fixed s > 1:

~~~text
spatial decay ratio = s^(-1) < 1
~~~

The oscillation sharpening uses:

~~~text
exp(-2*beta)  <= r <= exp(2*beta)
exp(-16*beta) <= R <= exp(16*beta)
~~~

so the sharpened amplitude vanishes at beta = 0.

The strict envelope coefficient is:

~~~text
c_env(beta,rho) = 18*eta(beta) + rho
~~~

and #4648 constructs a positive cutoff on which:

~~~text
c_env(beta, rho_osc(s,beta)) < 1
~~~

Consequences already integrated:

- strict maximum-column contraction for every finite volume/background;
- volume-independent complete-sweep exponential contraction.

**Status: closed.**

---

## 3. Ground-state L2 receiver — closed as infrastructure

### #4650: bounded-core closure

Integrated:

- six-spatial normalized residual energy on the genuine ground-state joint L2 carrier;
- continuity of the residual energy;
- dense bounded strongly measurable concrete core;
- coefficient-preserving extension from that core to the full joint L2 carrier.

### #4651: genuine six-spatial random-scan receiver

For the six genuine projections P_c:

~~~text
P_rs = (1/6) * sum_c P_c
inner(P_rs x, x) = (1/6) * sum_c ||P_c x||^2
~~~

Frame inequality:

~~~text
kappa * ||x||^2 <= (1/6) * sum_c ||x - P_c x||^2
~~~

is equivalent to:

~~~text
inner(P_rs x, x) <= (1-kappa) * ||x||^2
~~~

and any q < 1 in:

~~~text
inner(P_rs x, x) <= q * ||x||^2
~~~

feeds the physical transfer receiver:

~~~text
3*(1-q)/8 <= physical transfer gap
~~~

**Status: receiver closed; positive-beta quantitative premise open.**

---

## 4. Abstract commuting-projection tensorization — closed

PR #4652 proves the real-Hilbert theorem:

~~~text
||x - P_sweep x||^2 <= sum_c ||x - P_c x||^2
~~~

for a finite pairwise commuting family of self-adjoint idempotent projections.

Integrated ingredients:

1. norm contraction of self-adjoint idempotents;
2. pairwise commuting projections commute through finite sweeps;
3. coordinate defects do not increase;
4. one-step Pythagorean decomposition;
5. finite-list tensorization;
6. Fintype full-sweep tensorization.

**Status: closed.**

---

## 5. Exact beta-zero Wilson endpoint — closed through product laws

### #4653: ambient rank-one transfer

At beta = 0:

~~~text
K_0(A,B) = 1
T_0 = |1_Haar><1_Haar|
~~~

### #4654: physical Gauss-law rank-one transfer

At beta = 0:

- physical transfer is the self rank-one projection generated by the canonical physical constant-one unit vector;
- physical transfer norm = 1;
- normalized physical transfer is unchanged;
- the constant-one physical mode is fixed.

### #4655: canonical nonnegative vacuum

The selected abstract top eigenvector lies on the constant line and its canonical nonnegative representative is exactly the physical constant-one unit vector.

### #4656: exact probability laws

Exactly:

~~~text
vacuum_measure(beta=0) = spatial_Haar_measure
ground_state_joint_measure(beta=0) = pair_Haar_measure
~~~

No arbitrary L2 representative is evaluated pointwise.

**Status: closed.**

---

## 6. Current open theorem frontier — PR #4657

PR #4657 is open and remains non-authoritative until merged.

Target theorem:

~~~text
normalized beta-zero physical transfer
restricted to top-orthogonal sector = 0
~~~

Therefore:

~~~text
beta-zero finite-volume physical transfer gap = 1
~~~

independently of finite volume.

Current exact PR head at this docs refresh:

**521e2524b821df4cc0c7c46f580b247c2c669aa7**

Current CI state at this docs refresh:

- PR Lean Fast Check #14785 / run 35804699825;
- Changed Lean fast check is in progress.

### Acceptance criterion

Merge only after exact-head CI completion/success and then re-observe the theorem-carrier branch.

---

## 7. Next structural L2 frontier: beta-zero tensorization on the genuine joint law

After #4657, or independently of it, the next structural L2 unit is the model specialization of #4652.

### 7.1 Identify beta-zero six-spatial conditional expectations

Use the exact law:

~~~text
ground_state_joint_measure(beta=0) = pair_Haar_measure
~~~

to identify the six genuine right-boundary spatial conditional expectations with the corresponding product-Haar coordinate/color projections.

### 7.2 Prove pairwise commutation at beta zero

Required:

~~~text
P_c P_d = P_d P_c
~~~

for the genuine beta-zero six-spatial projection family.

Do not claim positive-beta commutativity.

### 7.3 Identify full sweep / common-fixed sector

#4652 controls:

~~~text
||x - P_sweep x||^2
~~~

The model theorem must identify the relevant sweep/common-fixed component on right-boundary physical lifts.

Prefer the already-defined ground-state coarse/retained center instead of inventing a parallel centering object.

### 7.4 Obtain beta-zero six-spatial frame / Rayleigh contraction

Apply #4652:

~~~text
||x - P_sweep x||^2 <= sum_c ||x - P_c x||^2
~~~

and convert it to the normalized six-spatial residual.

Then convert through #4651 to:

~~~text
inner(P_rs x, x) <= q0 * ||x||^2
~~~

with q0 < 1 on the required centered physical sector.

The exact q0 / kappa0 should be claimed only after the formal proof determines it.

### Acceptance criterion

A theorem on the genuine physical top-orthogonal/right-boundary sector with explicit q0 < 1 or kappa0 > 0, without inserting a new unproved Poincare assumption.

---

## 8. Positive-beta / high-temperature L2 bridge

The central remaining finite-volume quantitative theorem is a **volume-uniform** positive-beta version.

Available integrated inputs:

1. exact one-link ground-state conditional laws;
2. one-link conditional variance / residual identities;
3. physical influence / response estimates;
4. strict volume-independent physical sweep contraction (#4648);
5. exact beta-zero product law (#4656);
6. bounded-core closure (#4650);
7. Rayleigh receiver (#4651);
8. exact beta-zero transfer gap endpoint once #4657 is merged.

Missing theorem:

~~~text
physical interdependence coefficient < 1
    =>
genuine ground-state L2 Rayleigh coefficient < 1
~~~

with a coefficient independent of finite volume.

This may be formulated as a continuous-state Dobrushin / approximate-tensorization theorem, but it must match the actual ground-state conditional laws and the repository's target/source orientation.

### Required distinction

Do not identify bounded-test / total-variation-style influence contraction with L2 Rayleigh / Poincare contraction. The latter must be proved.

### Acceptance criterion

Produce q < 1, independent of the finite volume in the selected scaling family, such that:

~~~text
inner(P_rs x, x) <= q * ||x||^2
~~~

for every physical top-orthogonal state in the selected high-temperature regime.

Then #4651 yields:

~~~text
uniform transfer-gap lower bound = 3*(1-q)/8 > 0
~~~

---

## 9. Uniform finite-volume Hamiltonian gap

Once a scale-independent Rayleigh factor q < 1 is available:

1. apply the scale-uniform six-spatial transfer-gap receiver;
2. obtain a positive volume-independent physical transfer gap;
3. transport the bound to the exact Hamiltonian normalization;
4. identify the vacuum-orthogonal coercive estimate;
5. preserve the same-root physical carrier.

### Acceptance criterion

There exists gamma > 0, independent of finite volume, such that every member of the selected scaling family has physical excitation gap at least gamma.

This is still a lattice theorem, not yet the continuum mass gap.

---

## 10. Thermodynamic / infinite-volume construction

After the uniform finite-volume gap:

1. formalize compatible finite-volume embeddings / restrictions;
2. prove consistency of physical vacuum states;
3. establish the selected compactness / projective / direct-limit mechanism;
4. construct the infinite-volume Euclidean physical state;
5. transport reflection positivity, gauge invariance, and correlation bounds;
6. retain a nontrivial physical observable algebra.

The limiting carrier must remain the same-root physical Wilson/OS construction.

---

## 11. Continuum OS / Wightman construction

Required downstream units include:

- continuum Euclidean invariance;
- reflection positivity;
- regularity needed by the reconstruction theorem;
- cluster / decay statements strong enough for spectral interpretation;
- nontriviality of the physical Hilbert space and observable content;
- Wightman / OS reconstruction on the same physical theory.

Only after these are established can the continuum Hamiltonian be interpreted as the target Yang--Mills theory.

---

## 12. Continuum mass gap

The final theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a positive spectral lower edge on the vacuum-orthogonal sector.

The finite-volume constant must survive every limiting and identification step actually used.

A fixed-volume eigenvalue, auxiliary transfer matrix, or unrelated continuum limit is not by itself the Clay mass-gap conclusion.

---

## 13. Lean 4 / mathlib engineering rules

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Operational rules:

1. inspect the whole changed file, CompileSmoke, and import graph when CI fails;
2. do not infer mathematical failure from an elaboration failure;
3. match the existing universe declaration exactly;
4. use theorem rewrites before change when equality is not definitional;
5. verify Finset.sum_mul / mul_sum rewrite direction;
6. remember that rw can close a goal;
7. use ge_of_tendsto' / le_of_tendsto' with the correct inequality orientation;
8. keep local SU(N) topology/measurability instances narrowly scoped;
9. avoid broad import diamonds that redeclare pinned instances;
10. at Lp / a.e. boundaries, prefer explicit representative lemmas and calc chains;
11. avoid reverse rewriting with unconstrained implicit measure arguments;
12. reduce large operator equalities pointwise before elaborating global operator identities;
13. raise heartbeat / recursion limits only after signature, orientation, local-instance, and definitional-equality checks.

---

## 14. Recent canonical theorem units

| PR | Status | Role |
| --- | --- | --- |
| #4646 | merged | terminal covariance oscillation sharpening |
| #4647 | merged | beta-zero-vanishing remote residual |
| #4648 | merged | strict positive high-temperature physical sweep gate |
| #4650 | merged | six-spatial bounded-core L2 closure |
| #4651 | merged | genuine six-spatial random-scan Rayleigh receiver |
| #4652 | merged | finite tensorization for commuting Hilbert projections |
| #4653 | merged | beta-zero ambient transfer is rank one |
| #4654 | merged | beta-zero physical transfer is rank one |
| #4655 | merged | beta-zero canonical nonnegative vacuum is constant one |
| #4656 | merged | beta-zero vacuum/joint laws are Haar / pair Haar |
| #4657 | open | exact beta-zero physical transfer gap = 1; non-authoritative until merged |

Latest theorem-bearing merge before this docs refresh:

**245d422bef931e769434e2e8607c3d465b9e639b**

Latest validated integrated theorem head:

**fd209bdf7d32b7658d96db018ee7984f6f9621c0**

PR #4656 validation:

- PR Lean Fast Check #14782
- run 35802423074: success
- changed-Lean job 106995541127: success
- MCP completion receipt 106996352439: success
- exact-head status receipt: success

---

## 15. Short restart instruction

At the start of the next theorem thread:

1. fresh re-observe formal/real-hilbert-uniform-coercive-strong-limit;
2. do not use main as theorem authority;
3. distinguish docs-only pointer advances from theorem-bearing merges;
4. check #4657 state before using its exact beta-zero gap theorem;
5. after #4657, continue with beta-zero product-Haar specialization of #4652;
6. feed the resulting genuine six-spatial frame / Rayleigh theorem to #4651;
7. then construct the volume-uniform positive-beta L2 bridge.
