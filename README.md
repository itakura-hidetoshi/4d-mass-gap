# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository contains a large finite-volume Wilson / Osterwalder--Schrader / physical-transfer development together with the quantitative response, covariance, conditional-expectation, and Hilbert-space infrastructure intended to support a later uniform finite-volume gap and continuum construction.

## Current status — 2026-09-23 JST

The unique authoritative theorem-carrier branch is:

**formal/real-hilbert-uniform-coercive-strong-limit**

The theorem-bearing baseline immediately before this documentation refresh is:

**245d422bef931e769434e2e8607c3d465b9e639b**

This is the merge commit of PR #4656, **Identify exact beta-zero ground-state laws with Haar product laws**.

The default branch main is a public landing/documentation branch and is **not** theorem authority.

Fresh GitHub state always outranks this document. A later docs-only merge may advance a branch pointer without changing the theorem-bearing mathematical baseline.

> **Claim boundary.**
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
> What is integrated is a substantial finite-volume physical Wilson spine, including a canonical high-temperature strict physical sweep contraction and an exact beta-zero rank-one / product-Haar endpoint. The central remaining finite-volume obligation is a genuine L2 Poincare / Rayleigh estimate connecting the physical interdependence bounds to the ground-state conditional-expectation family. A uniform positive-beta finite-volume transfer/Hamiltonian gap and the thermodynamic/continuum construction remain downstream obligations.

## Repository authority

| Item | Value for this refresh |
| --- | --- |
| Theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Theorem-bearing baseline before docs refresh | 245d422bef931e769434e2e8607c3d465b9e639b |
| Latest integrated theorem PR | #4656 |
| Latest validated integrated theorem head | fd209bdf7d32b7658d96db018ee7984f6f9621c0 |
| Current open theorem PR | #4657 — exact beta-zero physical transfer gap; not yet authority |
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
  -> physical transfer operator and top sector
  -> ground-state transformed joint probability law
  -> genuine one-link conditional expectations

CANONICAL RESPONSE / HIGH-TEMPERATURE SPINE                 #4634-#4648
  -> literal fixed-right response continuity
  -> canonical compact-supremum / half-barrier closure
  -> actual physical weighted influence
  -> influence finite resolvent
  -> random-scan contraction
  -> covariance finite resolvent
  -> spatial random-scan resolvent
  -> actual spatial covariance clustering
  -> two-step terminal covariance decay
  -> cubic shell summability
  -> uniform physical remote residual
  -> oscillation sharpening vanishing at beta = 0
  -> positive strict-sweep cutoff
  -> volume-independent strict physical full-sweep contraction

GROUND-STATE L2 RECEIVER                                    #4650-#4652
  -> six-spatial residual energy on genuine joint L2
  -> bounded-concrete-core density closure
  -> genuine six-spatial random-scan Rayleigh receiver
  -> frame/Poincare <-> Rayleigh contraction identity
  -> transfer-gap receiver 3*(1-q)/8
  -> finite tensorization for commuting Hilbert projections

EXACT BETA-ZERO ENDPOINT                                    #4653-#4656
  -> ambient one-slab transfer = |1><1|
  -> physical Gauss-law transfer = |1><1|
  -> canonical nonnegative top vacuum = physical constant-one vector
  -> beta-zero vacuum measure = spatial Haar
  -> beta-zero ground-state joint measure = pair Haar

CURRENT OPEN FRONTIER                                       #4657
  -> prove normalized beta-zero physical transfer kills the top-orthogonal sector
  -> prove restricted transfer = 0
  -> conclude exact finite-volume beta-zero transfer gap = 1
  -> #4657 remains non-authoritative until merged

NEXT CANONICAL L2 UNIT
  -> specialize #4652 commuting-projection tensorization to the
     genuine beta-zero six-spatial ground-state conditional expectations
  -> identify the common-fixed / centered sector
  -> obtain a beta-zero six-spatial frame / Rayleigh contraction
  -> then build the volume-uniform positive-beta L2 bridge

DOWNSTREAM
  -> uniform positive-beta physical transfer/Hamiltonian gap
  -> thermodynamic / infinite-volume physical construction
  -> continuum OS / Wightman construction
  -> continuum Yang--Mills mass-gap theorem
~~~

## 1. Canonical high-temperature physical contraction is integrated

The old documentation stopped at the continuity of the literal fixed-right response (#4634). That is no longer the active frontier.

The integrated chain now runs through the actual physical influence and covariance machinery:

| PR | Integrated result |
| --- | --- |
| #4634 | Joint continuity of the literal fixed-right target-ratio response |
| #4637 | Canonical half-barrier closure |
| #4638 | Actual high-temperature physical weighted influence and response decay |
| #4639 | Weighted finite influence-path / resolvent propagation |
| #4640 | Canonical finite-volume random-scan contraction |
| #4641 | Canonical covariance finite-resolvent bound |
| #4642 | Spatial decay of the finite random-scan resolvent |
| #4643 | Actual spatial covariance clustering |
| #4644 | Concrete two-step terminal covariance spatial decay |
| #4645 | Volume- and background-uniform remote residual bound |
| #4646 | Oscillation-sharpened terminal covariance prefactor vanishing at beta zero |
| #4647 | Oscillation-sharpened remote residual vanishing at beta zero |
| #4648 | Strict physical sweep contraction on a positive canonical high-temperature interval |

For a fixed s > 1, the concrete terminal covariance decay ratio is:

~~~text
s^(-1) < 1
~~~

The oscillation-sharpened local amplitudes use the exact intervals already proved in the model:

~~~text
exp(-2*beta)  <= r <= exp(2*beta)
exp(-16*beta) <= R <= exp(16*beta)
~~~

so the sharpened terminal covariance amplitude contains:

~~~text
(exp(2*beta) - exp(-2*beta))
*
(exp(16*beta) - exp(-16*beta))
~~~

and therefore vanishes exactly at beta = 0.

The sharpened remote residual is inserted into the existing uniform envelope coefficient:

~~~text
c_env(beta,rho) = 18 * eta(beta) + rho
~~~

PR #4648 proves continuity at beta = 0 and constructs a strictly positive cutoff, contained in the canonical half-barrier interval, on which:

~~~text
c_env(beta, rho_osc(s,beta)) < 1
~~~

Integrated consequences:

- strict maximum-column contraction for every finite volume and background;
- volume-independent exponential contraction after a complete physical random-scan sweep.

This is a genuine physical finite-volume contraction result. It is **not** silently promoted to an L2 Poincare theorem.

## 2. The remaining L2 obligation is explicit

PRs #4650 and #4651 isolate the exact Hilbert-space receiver.

The genuine ground-state joint carrier has six actual right-boundary spatial conditional-expectation projections. Their normalized residual energy is defined directly on the full joint L2 space, and any quantitative estimate proved first on the dense bounded concrete core extends to the full carrier with no loss of coefficient.

PR #4651 defines the genuine six-spatial random-scan average:

~~~text
P_rs = (1/6) * sum_c P_c
~~~

and proves:

~~~text
inner(P_rs x, x) = (1/6) * sum_c ||P_c x||^2
~~~

Therefore the six-spatial frame inequality

~~~text
kappa * ||x||^2 <= (1/6) * sum_c ||x - P_c x||^2
~~~

is equivalent to the Rayleigh contraction

~~~text
inner(P_rs x, x) <= (1-kappa) * ||x||^2
~~~

The existing physical transfer receiver gives:

~~~text
3*(1-q)/8 <= physical top-eigenspace transfer gap
~~~

from any genuine six-spatial Rayleigh factor q <= 1, and gives a positive transfer gap when q < 1.

The finite-volume route therefore no longer has an ambiguous “Poincare step”: the missing model-facing theorem is the construction of a strict L2 frame / Rayleigh estimate for the genuine ground-state conditional-expectation family.

## 3. Abstract commuting-projection tensorization is proved

PR #4652 proves the real-Hilbert theorem needed at the decoupled endpoint.

For a finite family of pairwise commuting self-adjoint idempotent projections and an ordered full sweep P_sweep:

~~~text
||x - P_sweep x||^2 <= sum_c ||x - P_c x||^2
~~~

The proof establishes:

- self-adjoint idempotents are norm contractions;
- pairwise commuting projections commute through finite sweeps;
- coordinate defects do not increase under commuting projections;
- exact one-step Pythagorean decomposition;
- finite-list and Fintype full-sweep tensorization.

This theorem is pure Hilbert geometry and adds no Wilson-specific assumption.

## 4. Exact beta-zero transfer and vacuum are canonical

PRs #4653-#4656 close the decoupled endpoint normalization.

### Ambient transfer — #4653

At beta = 0 the literal temporal-gauge one-slab Wilson kernel is exactly 1.

Let 1_Haar be the normalized constant-one spatial Haar L2 vector. Then:

~~~text
K_0 = 1_Haar external-tensor 1_Haar
T_0 = |1_Haar><1_Haar|
~~~

### Physical Gauss-law transfer — #4654

The ambient identity descends to the genuine physical Gauss-law carrier:

- the physical transfer is the self rank-one projection generated by the canonical physical constant-one unit vector;
- the physical transfer norm is exactly one;
- the normalized physical transfer is unchanged;
- the canonical physical constant-one vector is fixed.

### Canonical nonnegative vacuum — #4655

The selected abstract top eigenvector lies on the constant line. Unit normalization fixes the scalar absolute value, and compatibility of real L2 absolute value with scalar multiplication removes the sign ambiguity.

Therefore the canonical nonnegative physical top eigenvector at beta = 0 is exactly the physical constant-one unit vector.

### Exact probability laws — #4656

The proof stays at the a.e. representative level until the final measure equalities. It proves exactly:

~~~text
vacuum_measure(beta=0) = spatial_Haar_measure
ground_state_joint_measure(beta=0) = pair_Haar_measure
~~~

No arbitrary L2 equivalence-class representative is evaluated pointwise.

## 5. Current open theorem PR: #4657

PR #4657 is open and is **not** part of theorem authority yet.

It uses the already integrated exact physical rank-one transfer to target the stronger endpoint statement:

~~~text
normalized beta-zero physical transfer
restricted to the full top-orthogonal sector = 0
~~~

and therefore:

~~~text
beta-zero finite-volume physical transfer gap = 1
~~~

independently of finite volume.

Because #4657 is open and its head can move, this document does not pin its exact head or CI receipt. Re-observe the PR before using it. Until it is merged, the authoritative theorem-bearing baseline remains #4656.

## 6. Next L2 theorem unit after the exact beta-zero gap

The next canonical L2 unit should use the exact product law from #4656 and the abstract tensorization theorem from #4652.

Target sequence:

1. identify the six beta-zero ground-state spatial conditional expectations with the corresponding product-Haar coordinate/color projections;
2. prove the required pairwise commutation on the genuine joint L2 carrier;
3. identify the full sweep / common-fixed component;
4. apply #4652 to obtain the beta-zero six-spatial frame estimate;
5. convert it through #4651 to a genuine six-spatial Rayleigh contraction.

The exact transfer-gap theorem #4657 gives a strong independent endpoint check, but it does not replace the six-spatial L2 bridge needed for positive beta.

## 7. Positive-beta high-temperature L2 bridge

The repository already has:

- exact one-link ground-state conditional laws;
- one-link conditional variance / residual identities;
- strict volume-independent physical influence contraction (#4648);
- exact beta-zero product law (#4656);
- dense-core closure (#4650);
- genuine Rayleigh receiver (#4651).

The missing theorem must rigorously connect:

~~~text
physical interdependence coefficient < 1
~~~

to

~~~text
genuine ground-state L2 Rayleigh coefficient < 1
~~~

with a constant independent of finite volume.

The repository intentionally keeps bounded-test / total-variation-style influence control distinct from L2 Rayleigh / Poincare coercivity.

## 8. Downstream obligations

After a scale-independent positive L2 frame / Rayleigh coefficient is proved, existing receivers can produce a uniform finite-volume physical transfer gap.

Still separate:

- exact Hamiltonian coercive lower bound in the selected normalization;
- scaling-family transport;
- thermodynamic / infinite-volume physical state;
- continuum OS construction;
- Euclidean axioms / nontriviality on the same-root physical carrier;
- Wightman reconstruction / spectral interpretation;
- continuum Yang--Mills mass gap.

A fixed-volume isolated top eigenvalue is not a volume-uniform gap. A volume-uniform lattice gap is not automatically a continuum Yang--Mills construction.

## Lean / mathlib verification discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6

Recent proof-engineering rules:

- match the universe declared by the existing structure; do not replace Type with Type* without checking;
- change only closes definitional equality; perform theorem-level normalization first;
- check Finset.sum_mul / mul_sum rewrite direction explicitly;
- rw may close a goal, so a following tactic can legitimately report “no goals to be solved”;
- at Lp / a.e. representative boundaries, prefer explicit calc chains to fragile rewrites;
- avoid reverse rewriting with theorems whose important measure argument is still implicit and unconstrained;
- reduce large operator equalities pointwise before asking the elaborator to normalize them;
- keep local SU(N) topology/measurability instances narrowly scoped;
- avoid broad import diamonds that redeclare pinned instances;
- do not raise heartbeat / recursion depth before checking signatures, rewrite orientation, local instances, and definitional equality;
- inspect the full changed module, CompileSmoke, and dependency graph, not only the highlighted CI line.

### Latest integrated exact-head validation

PR #4656:

- validated head: fd209bdf7d32b7658d96db018ee7984f6f9621c0
- PR Lean Fast Check #14782 / run 35802423074: success
- Changed Lean fast check job 106995541127: success
- MCP completion receipt 106996352439: success
- exact-head status receipt: success

The theorem-bearing merge commit is:

**245d422bef931e769434e2e8607c3d465b9e639b**

## Navigation

- ROADMAP.md — detailed completed and remaining theorem units.
- MGAP4D/MathlibAnalytic — formal analytic development.
- Theorem-carrier branch: https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit

## Status summary

The repository has moved materially beyond response continuity.

The integrated formal state includes:

- canonical high-temperature response / influence control;
- actual spatial covariance clustering;
- terminal covariance and cubic-shell summability;
- a uniform physical remote residual;
- a positive strict physical full-sweep contraction interval;
- genuine six-spatial L2 Poincare / Rayleigh receivers;
- abstract commuting-projection tensorization;
- exact beta-zero rank-one ambient and physical transfer;
- exact canonical beta-zero vacuum;
- exact beta-zero Haar / pair-Haar ground-state laws.

Current open theorem work is #4657, targeting the exact beta-zero physical transfer gap = 1. The next structural L2 frontier is the beta-zero specialization of #4652 tensorization to the genuine six-spatial conditional-expectation family, followed by the volume-uniform positive-beta L2 bridge.
