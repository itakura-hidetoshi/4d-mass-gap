# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, together with exact beta-zero geometry, response and covariance control, conditional expectations, Hilbert-space tensorization, spectral-gap receivers, and downstream thermodynamic/continuum infrastructure.

## Current status — 2026-09-23 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh GitHub state at this documentation refresh:

**bbd064ddff7814a804c2ba319e6c365dabd9ecb4**

This is the merge commit of PR #4678, **Bridge beta-zero physical top-orthogonal sector to pair-Haar boundary geometry**. It also contains the immediately preceding merged PR #4677, **Prove beta-zero physical pair-Haar orthogonal bridge**.

The default branch **main** is a public landing/documentation branch and is **not** theorem authority.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
> What is now integrated is a substantial finite-volume Wilson/OS/physical-transfer theorem spine. In particular, the beta-zero six-spatial pair-Haar projection geometry is closed through exact frame/Rayleigh constants, and the genuine physical beta-zero top-orthogonal sector has now been bridged into that pair-Haar boundary geometry. The main quantitative frontier is the volume-uniform positive-beta ground-state L2 bridge, followed by thermodynamic and continuum construction.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Current theorem-bearing baseline | bbd064ddff7814a804c2ba319e6c365dabd9ecb4 |
| Latest merged theorem PR | #4678 |
| Immediately preceding merged theorem PR | #4677 |
| #4677 validated exact head | d5da7f0c97f4c736f2e7a41015c003ab1a899a3b |
| #4677 CI | PR Lean Fast Check #14856 / run 35850382949 — success |
| #4678 validated exact head | 43f73b187073e47b678fd5d9f229646c28d97f27 |
| #4678 CI | PR Lean Fast Check #14855 / run 35850140311 — success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |
| Default branch | main — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A later docs-only merge may advance a branch pointer without changing the theorem-bearing mathematical baseline.

## Proof spine at a glance

~~~text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT
  -> periodic SU(N) Wilson one-slab kernel
  -> OS / Gauss-law physical carrier
  -> compact positive physical transfer
  -> top eigenspace / canonical nonnegative vacuum
  -> ground-state transformed boundary and joint laws
  -> genuine conditional-expectation families

HIGH-TEMPERATURE RESPONSE / PHYSICAL SWEEP                  #4634-#4648
  -> fixed-right response continuity
  -> canonical half-barrier closure
  -> actual physical influence / finite resolvent
  -> random-scan contraction and covariance resolvent
  -> spatial covariance clustering
  -> terminal covariance decay / shell summability
  -> beta-zero-vanishing sharpened residual
  -> positive volume-independent strict physical full-sweep contraction

GROUND-STATE L2 RECEIVER / ABSTRACT TENSORIZATION           #4650-#4652
  -> six-spatial residual energy on genuine joint L2
  -> bounded-core closure
  -> six-spatial random-scan Rayleigh receiver
  -> frame/Poincare <-> Rayleigh identity
  -> physical transfer-gap receiver 3*(1-q)/8
  -> finite tensorization for pairwise commuting Hilbert projections

EXACT BETA-ZERO PHYSICAL ENDPOINT                           #4653-#4657
  -> ambient transfer = |1><1|
  -> physical transfer = |1><1|
  -> canonical nonnegative vacuum = constant-one
  -> vacuum law = spatial Haar
  -> ground-state joint law = pair Haar
  -> top-orthogonal normalized transfer = 0
  -> exact finite-volume physical transfer gap = 1

BETA-ZERO SIX-SPATIAL PAIR-HAAR GEOMETRY                    #4662-#4676
  -> literal pair-Haar L2 carrier and Fin 6 projections
  -> color/off-color product decomposition
  -> common-fixed intersection = boundary L2
  -> idempotence / symmetry
  -> product conditional-expectation fiber formula
  -> range-invariance -> commutation Hilbert receiver
  -> shared-base conditional-expectation collapse
  -> Wilson-specific range invariance
  -> actual pairwise commutation
  -> actual full-sweep tensorization
  -> full-sweep fixed sector = fst-boundary L2
  -> sweep = orthogonal projection
  -> exact frame coefficient kappa_0 = 1/6
  -> exact random-scan Rayleigh factor q_0 = 5/6

PHYSICAL BETA-ZERO -> PAIR-HAAR BOUNDARY BRIDGE             #4677-#4678
  -> literal right-boundary pair-Haar L2 isometry
  -> physical top-orthogonal -> fst-boundary orthogonal
  -> beta-zero Haar-to-vacuum isometry is onto
  -> ambient rank-one annihilation -> Doob boundary image = 0
  -> coarse left-boundary projection of transformed right lift = 0

IMMEDIATE ENDPOINT PACKAGING
  -> apply #4676 to the #4677 / #4678 physical bridge
  -> package genuine physical beta-zero six-spatial kappa_0 = 1/6
  -> package genuine physical beta-zero q_0 = 5/6
  -> feed #4651 for the consistency lower bound 1/16
  -> retain #4657 gap_beta=0 = 1 as the exact endpoint value

MAIN QUANTITATIVE FRONTIER
  -> volume-uniform positive-beta ground-state L2 bridge
  -> uniform finite-volume physical transfer / Hamiltonian gap
  -> thermodynamic / infinite-volume physical construction
  -> continuum OS / Wightman construction
  -> continuum Yang--Mills positive spectral gap
~~~

## 1. High-temperature physical contraction is integrated

The response/covariance chain #4634-#4648 is no longer the active obstruction. It reaches a genuine volume-independent strict physical sweep contraction on a positive high-temperature interval.

This is a finite-volume physical contraction theorem. It is deliberately **not** identified with an L2 Poincare/Rayleigh theorem without an explicit bridge.

## 2. The genuine L2 receiver is integrated

PR #4650 closes the bounded-core-to-full-L2 extension for the six-spatial residual energy.

PR #4651 defines the genuine six-spatial random scan

~~~text
P_rs = (1/6) * sum_c P_c
~~~

and proves the Hilbert identity behind

~~~text
kappa * ||x||^2 <= (1/6) * sum_c ||x - P_c x||^2
~~~

if and only if

~~~text
inner(P_rs x, x) <= (1-kappa) * ||x||^2.
~~~

The physical receiver converts any genuine q < 1 into

~~~text
3*(1-q)/8 <= physical transfer gap.
~~~

PR #4652 provides the finite tensorization inequality for pairwise commuting self-adjoint idempotent projections.

## 3. The exact beta-zero physical endpoint is closed

PRs #4653-#4657 prove, at beta = 0,

~~~text
ambient transfer = |1_Haar><1_Haar|
physical transfer = |1_phys><1_phys|
vacuum measure = spatial Haar
ground-state joint measure = pair Haar
~~~

and on the full physical top-orthogonal sector

~~~text
normalized physical transfer = 0
physical transfer gap = 1.
~~~

The exact gap value one is finite-volume and volume-independent. It is not by itself a positive-beta or continuum mass gap.

## 4. Beta-zero six-spatial pair-Haar geometry is now closed

The structural lane that was still open at #4668 is now complete.

| PR | Integrated role |
| --- | --- |
| #4662 | Literal pair-Haar joint L2 carrier and Fin 6 spatial projections |
| #4663 | Exact color/off-color Haar product decomposition |
| #4664 | Six-retained common-fixed intersection = complete boundary L2 |
| #4665 | Projection idempotence and symmetry |
| #4666 | Product-probability conditional-expectation fiber formula |
| #4667 | Hilbert receiver: range invariance -> projection commutation |
| #4668 | Shared-base three-factor conditional-expectation collapse |
| #4671 | Wilson-specific pair-Haar range invariance |
| #4672 | Actual pairwise commutation of the six projections |
| #4673 | Actual full-sweep tensorization and fixed-sector criterion |
| #4674 | Full-sweep fixed sector = fst-boundary L2 |
| #4676 | Sweep orthogonal geometry, exact kappa_0=1/6 and q_0=5/6 |

PR #4675 was **closed unmerged and superseded by #4676**. It must not be revived as theorem authority.

The exact beta-zero literal pair-Haar conclusions are:

~~~text
(1/6) * ||x||^2
  <= (1/6) * sum_c ||x - P_c x||^2

inner(P_rs x, x)
  <= (5/6) * ||x||^2
~~~

for vectors in the complete fst-boundary orthogonal complement.

## 5. The physical beta-zero boundary bridge is integrated

PR #4677 proves the direct literal-carrier bridge:

~~~text
physical beta-zero top-orthogonal
  -> literal pair-Haar right-boundary lift
  -> fst-boundary orthogonal complement.
~~~

Its generic product-probability lemma says that a snd-measurable L2 vector with zero mean lies in the orthogonal complement of the complete fst-measurable L2 subspace.

PR #4678 provides the complementary Doob/coarse-projection route:

~~~text
ambient beta-zero transfer kills f
  -> D_0(U_0 f) = 0
  -> Q_0(R_0(U_0 f)) = 0.
~~~

Together these close the obstruction that previously separated the genuine physical beta-zero excitation sector from the pair-Haar six-spatial geometry.

## 6. Immediate next theorem unit

The remaining beta-zero work is now packaging rather than new geometry.

Use #4677 (or equivalently the #4678 coarse-projection route) to place the transformed physical top-orthogonal vector in the hypothesis of #4676, then use the existing linear isometries to transport norms.

The expected packaged conclusions are:

~~~text
kappa_0 = 1/6
q_0 = 5/6
~~~

on the genuine physical beta-zero six-spatial sector.

Feeding q_0 = 5/6 into #4651 gives the consistency lower bound

~~~text
3*(1 - 5/6)/8 = 1/16.
~~~

This is not the optimal beta-zero transfer gap: #4657 already proves the exact value

~~~text
gap_beta=0 = 1.
~~~

The value 1/16 is a consistency receipt for the six-spatial Rayleigh route.

## 7. Main quantitative frontier: positive-beta volume-uniform L2 bridge

The repository now has both sides that must be connected:

~~~text
strict volume-independent physical influence/sweep contraction     #4648
exact/genuine six-spatial L2 Rayleigh receiver                     #4651
closed beta-zero pair-Haar tensorization and physical bridge       #4662-#4678
~~~

The missing theorem is a volume-uniform implication of the form

~~~text
physical interdependence coefficient < 1
    =>
genuine ground-state L2 Rayleigh coefficient < 1
~~~

for positive beta in a high-temperature interval.

Bounded-test / total-variation influence control and L2 Poincare/Rayleigh coercivity remain distinct until this theorem is proved.

## 8. Downstream obligations

After a scale-independent positive-beta L2 coefficient is proved:

1. obtain a uniform finite-volume physical transfer gap through the existing receiver;
2. transport it to Hamiltonian vacuum-orthogonal coercivity;
3. construct the thermodynamic/infinite-volume physical state;
4. preserve reflection positivity, gauge invariance, nontrivial observables, and same-root authority;
5. construct the continuum OS theory;
6. perform Wightman/OS reconstruction;
7. prove a unique continuum vacuum and a positive lower spectral edge on its orthogonal complement.

A fixed-volume gap is not automatically a continuum Yang--Mills mass gap.

## Lean / mathlib verification discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Current proof-engineering rules:

- inspect the whole changed module, imports, CompileSmoke, and dependent API when CI fails;
- treat the pinned mathlib revision as authority rather than current master;
- keep dependent Lp measure transport narrow; do not rewrite a proof-indexed Lp type wholesale;
- make product measurable spaces explicit when conditional-expectation APIs introduce independent ambient measurable-space metavariables;
- prefer literal `Prod.instMeasurableSpace` when the product sigma-algebra must be definitionally shared;
- keep ContinuousLinearMap / LinearMap / LinearIsometry coercion boundaries explicit;
- use `change` only for definitional equality;
- remember that `rw` needs a syntactic occurrence after elaboration; unfold wrappers before representative-level rewrites;
- use `simp only` when global simp lemmas would destroy the local representative shape needed by the proof;
- separate structural simplification from arithmetic normalization; use `norm_num` for exact rational identities;
- avoid expensive orthogonal-projection instance synthesis when a direct inner-product characterization proves membership in an orthogonal complement;
- validate the exact PR head and confirm the exact-head completion receipt before merging.

### Recent exact-head validation

- #4676 head `ca05fcd095e84d5f3f56b1ae3cb2c4bc56b3ae52` — Fast Check #14843 / run 35843054541: success.
- #4677 head `d5da7f0c97f4c736f2e7a41015c003ab1a899a3b` — Fast Check #14856 / run 35850382949: success.
- #4678 head `43f73b187073e47b678fd5d9f229646c28d97f27` — Fast Check #14855 / run 35850140311: success.

Current theorem-bearing baseline before this docs refresh:

**bbd064ddff7814a804c2ba319e6c365dabd9ecb4**

## Navigation

- `ROADMAP.md` — detailed completed and remaining theorem units.
- `MGAP4D/MathlibAnalytic` — formal analytic development.
- Theorem-carrier branch: `formal/real-hilbert-uniform-coercive-strong-limit`.

## Status summary

Integrated formal state now includes:

- volume-independent high-temperature physical response/influence contraction;
- genuine six-spatial L2 Rayleigh receivers;
- abstract finite tensorization for commuting Hilbert projections;
- exact beta-zero rank-one ambient and physical transfer;
- exact beta-zero vacuum and pair-Haar joint laws;
- exact finite-volume beta-zero physical transfer gap = 1;
- complete literal beta-zero six-spatial pair-Haar projection geometry;
- actual pairwise commutation and full-sweep tensorization;
- exact common-fixed boundary identification;
- exact literal beta-zero frame coefficient `kappa_0 = 1/6`;
- exact literal beta-zero random-scan factor `q_0 = 5/6`;
- direct and Doob/coarse-projection bridges from the genuine physical beta-zero excitation sector into the pair-Haar boundary geometry.

The immediate small endpoint task is to package the genuine physical beta-zero six-spatial `kappa_0=1/6`, `q_0=5/6` theorem. The major finite-volume quantitative frontier is then the **volume-uniform positive-beta L2 bridge**.
