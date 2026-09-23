# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository contains a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer development, together with response, covariance, conditional-expectation, Hilbert-space, and projective-limit infrastructure intended to support a later volume-uniform gap and continuum construction.

## Current status — 2026-09-23 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

The theorem-bearing baseline immediately before this documentation refresh is:

**1071479971e78354deae2d7904dc8f6d2fe8a5b0**

This is the merge commit of PR #4668, **Prove shared-base product conditional expectation collapse**.

The default branch **main** is the public landing/documentation branch and is **not** theorem authority. Fresh GitHub state always outranks this document. A later docs-only merge may advance a branch pointer without changing the theorem-bearing mathematical baseline.

> **Claim boundary.**
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
> What is integrated is a substantial finite-volume Wilson/OS/physical-transfer spine. In particular, the repository now contains a volume-independent high-temperature physical sweep contraction, an exact beta-zero rank-one physical transfer with finite-volume transfer gap exactly one, the genuine six-spatial L2 receiver, and most of the product-Haar / commuting-projection infrastructure needed for the beta-zero six-spatial tensorization. The Wilson-specific pairwise range-invariance/commutation step and a volume-uniform positive-beta L2 Poincare/Rayleigh theorem remain open, followed by thermodynamic and continuum construction.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Theorem-bearing baseline before docs refresh | 1071479971e78354deae2d7904dc8f6d2fe8a5b0 |
| Latest integrated theorem PR | #4668 |
| Latest validated #4668 exact head | 5d2c0010e11c8e40d8836443e7d168b7d520d4be |
| Latest exact-head CI | PR Lean Fast Check #14817 / run 35822417043 — success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |
| Default branch | main — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean artifacts;
3. README / ROADMAP;
4. CI receipts;
5. historical summaries or memory.

## Proof spine at a glance

~~~text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT
  -> periodic SU(N) Wilson one-slab kernel
  -> OS / Gauss-law physical carriers
  -> compact positive physical transfer
  -> top eigenspace / canonical nonnegative vacuum
  -> ground-state transformed joint law
  -> genuine conditional-expectation families

HIGH-TEMPERATURE RESPONSE / PHYSICAL SWEEP                 #4634-#4648
  -> fixed-right response continuity
  -> canonical half-barrier closure
  -> actual physical influence and finite resolvent
  -> random-scan contraction and covariance resolvent
  -> spatial covariance clustering
  -> terminal covariance decay / cubic-shell summability
  -> beta-zero-vanishing remote residual
  -> positive volume-independent strict physical full-sweep contraction

GROUND-STATE L2 RECEIVER / ABSTRACT TENSORIZATION          #4650-#4652
  -> six-spatial residual energy on genuine joint L2
  -> bounded-concrete-core closure
  -> six-spatial random-scan Rayleigh receiver
  -> frame/Poincare <-> Rayleigh identity
  -> physical transfer-gap receiver 3*(1-q)/8
  -> finite tensorization for pairwise commuting Hilbert projections

EXACT BETA-ZERO PHYSICAL ENDPOINT                          #4653-#4657
  -> ambient transfer = |1><1|
  -> physical transfer = |1><1|
  -> canonical nonnegative vacuum = constant-one mode
  -> vacuum law = spatial Haar
  -> ground-state joint law = pair Haar
  -> top-orthogonal normalized transfer = 0
  -> exact finite-volume physical transfer gap = 1

BETA-ZERO SIX-SPATIAL PRODUCT-HAAR SPINE                  #4662-#4668
  -> literal pair-Haar joint L2 carrier and Fin 6 color projections
  -> exact color/off-color Haar splitting
  -> six-retained common-fixed range = boundary L2
  -> each color projection is idempotent and symmetric
  -> product-probability conditional expectation = fiber integral
  -> range invariance + Hilbert geometry => projection commutation
  -> shared-base three-factor conditional expectation collapses to common base

CURRENT MODEL-SPECIFIC FRONTIER
  -> transport the shared-base collapse through the actual Wilson color coordinates
  -> prove P_c(range P_d) subset range P_d for every pair of spatial colors
  -> apply #4667 to obtain genuine beta-zero pairwise commutation
  -> apply #4652 and the #4664 common-fixed identification
  -> obtain an explicit beta-zero six-spatial frame/Rayleigh constant
  -> then build the volume-uniform positive-beta L2 bridge

DOWNSTREAM
  -> uniform positive-beta physical transfer/Hamiltonian gap
  -> thermodynamic / infinite-volume physical construction
  -> continuum OS / Wightman construction
  -> continuum Yang--Mills mass-gap theorem
~~~

## 1. Canonical high-temperature physical contraction is integrated

The response/covariance chain is no longer the active obstruction. The integrated sequence #4634-#4648 reaches a genuine volume-independent strict physical sweep contraction on a positive high-temperature interval.

For fixed s > 1, the spatial decay ratio is:

~~~text
s^(-1) < 1
~~~

The oscillation sharpening uses the proved intervals

~~~text
exp(-2*beta)  <= r <= exp(2*beta)
exp(-16*beta) <= R <= exp(16*beta)
~~~

and therefore vanishes exactly at beta = 0. The sharpened residual enters the envelope

~~~text
c_env(beta,rho) = 18*eta(beta) + rho
~~~

and #4648 constructs a positive cutoff on which c_env < 1.

This is a physical finite-volume contraction theorem. It is not silently identified with an L2 Poincare theorem.

## 2. The genuine L2 receiver and abstract tensorization are integrated

PR #4650 closes the dense-core-to-full-L2 extension for the genuine six-spatial residual energy.

PR #4651 defines the genuine six-spatial random-scan average

~~~text
P_rs = (1/6) * sum_c P_c
~~~

and proves the exact Hilbert identity

~~~text
inner(P_rs x, x) = (1/6) * sum_c ||P_c x||^2.
~~~

Hence

~~~text
kappa * ||x||^2 <= (1/6) * sum_c ||x - P_c x||^2
~~~

is equivalent to

~~~text
inner(P_rs x, x) <= (1-kappa) * ||x||^2.
~~~

The physical receiver converts any genuine q < 1 into

~~~text
3*(1-q)/8 <= physical transfer gap.
~~~

PR #4652 proves the abstract finite tensorization theorem for pairwise commuting self-adjoint idempotent Hilbert projections:

~~~text
||x - P_sweep x||^2 <= sum_c ||x - P_c x||^2.
~~~

Thus the missing step is now model-facing: establish the hypotheses and the centered/common-fixed geometry for the actual beta-zero six-spatial family.

## 3. The exact beta-zero physical endpoint is closed

PRs #4653-#4657 now give the full finite-volume decoupled endpoint.

At beta = 0:

~~~text
ambient transfer = |1_Haar><1_Haar|
physical transfer = |1_phys><1_phys|
vacuum_measure = spatial_Haar
ground_state_joint_measure = pair_Haar
~~~

PR #4657 additionally proves:

~~~text
normalized physical transfer
restricted to the full top-orthogonal sector = 0

operator norm of that restriction = 0

finite-volume physical transfer gap = 1
~~~

The value 1 is exact and independent of finite volume. This is an endpoint finite-volume theorem; it is not by itself a positive-beta uniform gap or continuum mass gap.

## 4. Beta-zero six-spatial product-Haar specialization is now largely structural

The post-#4657 chain separates measure theory, Hilbert geometry, and Wilson-specific coordinate transport.

| PR | Integrated role |
| --- | --- |
| #4662 | Exposes the literal pair-Haar joint L2 carrier and the Fin 6 spatial-color conditional-expectation projections |
| #4663 | Splits a selected right-boundary color block from the off-color block by a measure-preserving product-Haar equivalence |
| #4664 | Identifies the intersection of the six right-retained L2 ranges with the full left-boundary L2 subspace; symmetrically for the left family |
| #4665 | Proves each literal pair-Haar color projection is idempotent and symmetric/self-adjoint |
| #4666 | Proves the generic product-probability conditional-expectation fiber formula |
| #4667 | Proves the Hilbert receiver: range invariance of Q under symmetric P implies commutation with symmetric idempotent Q |
| #4668 | Proves the three-factor shared-base collapse: right-retained data averaged onto left-retained data becomes common-base measurable |

The architecture is now:

~~~text
product-Haar Fubini / shared-base collapse     #4666, #4668
                  |
                  v
Wilson color-coordinate range invariance       NEXT
                  |
                  v
Hilbert range-invariance receiver              #4667
                  |
                  v
pairwise commutation of six beta-zero P_c
                  |
                  v
finite tensorization                            #4652
                  |
                  v
common-fixed = boundary L2                     #4664
                  |
                  v
beta-zero six-spatial frame / Rayleigh bound   NEXT
~~~

No positive-beta commutativity is claimed.

## 5. Current theorem frontier

The next minimal theorem unit should be Wilson-specific rather than another generic probability lemma.

For every pair of beta-zero spatial colors c,d, prove on the literal pair-Haar joint L2 carrier:

~~~text
P_c (range P_d) subset range P_d.
~~~

The intended route is:

1. use the color/off-color and retained-coordinate measurable equivalences already integrated;
2. reindex the two retained sigma-algebras into a three-factor product with a common base;
3. apply #4668 so the cross conditional expectation collapses to the common-base information;
4. conclude range invariance;
5. apply #4667 to obtain P_c P_d = P_d P_c.

Once pairwise commutation is formal, #4652 can be applied directly. The resulting sweep/common-fixed term should be connected to the already-proved #4664 boundary-L2 identification rather than introducing a duplicate centering object.

The exact beta-zero constants kappa0 and q0 should be stated only after Lean determines them. The documentation does not pre-commit to a numerical constant.

## 6. Positive-beta high-temperature L2 bridge remains the central finite-volume quantitative obligation

The repository already has:

- exact ground-state conditional laws;
- one-link conditional variance/residual identities;
- strict volume-independent physical influence contraction (#4648);
- exact beta-zero product law (#4656);
- exact beta-zero physical transfer gap = 1 (#4657);
- dense-core closure (#4650);
- genuine six-spatial Rayleigh receiver (#4651);
- nearly complete beta-zero product-Haar tensorization infrastructure (#4662-#4668).

The still-missing positive-beta theorem must rigorously connect

~~~text
physical interdependence coefficient < 1
~~~

to

~~~text
genuine ground-state L2 Rayleigh coefficient < 1
~~~

with a coefficient independent of finite volume.

Bounded-test / total-variation-style influence control and L2 Poincare/Rayleigh coercivity remain deliberately distinct until a theorem connects them.

## 7. Downstream obligations

After a scale-independent positive-beta L2 coefficient is proved:

1. obtain a uniform finite-volume physical transfer gap through the existing receiver;
2. transport it to the selected Hamiltonian normalization and vacuum-orthogonal coercivity statement;
3. construct a compatible thermodynamic / infinite-volume physical state;
4. preserve reflection positivity, gauge invariance, nontrivial observables, and the same-root physical carrier;
5. construct the continuum OS theory and Wightman reconstruction;
6. prove the continuum Hamiltonian has a unique vacuum and a positive lower spectral edge on the vacuum-orthogonal sector.

A fixed-volume gap, even an exact one, is not automatically a volume-uniform positive-beta gap. A uniform lattice gap is not automatically a continuum Yang--Mills construction.

## Lean / mathlib verification discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Current proof-engineering rules:

- inspect the entire changed module, CompileSmoke, imports, and dependent API when CI fails;
- treat the pinned mathlib revision as authority: a module path visible on current mathlib master may not exist at the repository pin;
- check theorem namespaces at the pinned revision before using field notation;
- note that IsIdempotentElem may elaborate as an equality, so a namespace theorem such as LinearMap.IsIdempotentElem.commute_iff may need a fully qualified call;
- keep ContinuousLinearMap / LinearMap coercion boundaries explicit when an API is stated only for one of them;
- change closes definitional equality only; perform theorem-level normalization first when required;
- at Lp / a.e. boundaries, prefer explicit representative lemmas and calc chains to fragile rewrites;
- avoid reverse rewriting through unconstrained implicit measure arguments;
- reduce large operator equalities pointwise before asking the elaborator to normalize them;
- keep local SU(N) topology/measurability instances narrowly scoped;
- do not raise heartbeat or recursion limits before checking signatures, rewrite direction, local instances, and definitional equality;
- validate the exact PR head and then confirm the completion-receipt status before merging.

### Recent exact-head validation

- #4666 head 04e79a500a4a33b92ab4f6021aaf650e34ab94d7 — PR Lean Fast Check #14810 / run 35819293208: success.
- #4667 head 174886cec0e2c79864dffaf988e597f2d29cb7de — PR Lean Fast Check #14815 / run 35821420342: success.
- #4668 synchronized head 5d2c0010e11c8e40d8836443e7d168b7d520d4be — PR Lean Fast Check #14817 / run 35822417043: success.

The theorem-bearing baseline before this docs refresh is:

**1071479971e78354deae2d7904dc8f6d2fe8a5b0**

## Navigation

- ROADMAP.md — detailed completed and remaining theorem units.
- MGAP4D/MathlibAnalytic — formal analytic development.
- Theorem-carrier branch: https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit

## Status summary

The integrated formal state now includes:

- canonical high-temperature response/influence control and strict physical full-sweep contraction;
- genuine six-spatial L2 Poincare/Rayleigh receivers;
- abstract finite tensorization for commuting Hilbert projections;
- exact beta-zero rank-one ambient and physical transfer;
- exact beta-zero vacuum and pair-Haar joint laws;
- exact finite-volume beta-zero physical transfer gap = 1;
- literal beta-zero pair-Haar six-spatial projections;
- exact six-retained common-fixed boundary-L2 geometry;
- idempotence and symmetry of the six beta-zero projections;
- product-probability fiber conditional-expectation and shared-base collapse theorems;
- a generic Hilbert theorem reducing pairwise commutation to range invariance.

The immediate frontier is the **Wilson-specific pairwise range-invariance theorem** that connects #4668 to #4667. After that, the beta-zero six-spatial tensorization should close and feed the genuine Rayleigh receiver. The major remaining finite-volume quantitative problem is then the volume-uniform positive-beta L2 bridge.
