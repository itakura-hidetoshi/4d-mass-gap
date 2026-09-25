# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory. The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta physical response and covariance control, genuine ground-state conditional expectations, Hilbert-space coercivity receivers, and downstream thermodynamic / continuum infrastructure.

## Current status — 2026-09-25 JST

The unique authoritative theorem-carrier branch is:

**`formal/real-hilbert-uniform-coercive-strong-limit`**

The fresh theorem-bearing baseline immediately before this documentation refresh is:

**`e4c878398f0d0aa183cfc86eb8970c7c3593114e`**

This is the merge commit of PR **#4773**, **Integrate background-dependent Schur coercivity over outer law**.

The default branch **`main` is not theorem authority**.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is integrated is a substantial finite-volume Wilson / OS / physical-transfer theorem spine. The exact beta-zero endpoint is closed. The positive-beta physical influence side has a volume-independent strict bidirectional Schur coefficient. The genuine six-spatial sweep local-energy side is closed. The former coefficient-one localPart obstruction is now closed through the actual sweep-stage local profile. The current frontier is the final observable-specific response / one-sided recurrence instantiation and its integration into the positive-beta bounded-core Poincare theorem.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Theorem-bearing baseline before this docs refresh | `e4c878398f0d0aa183cfc86eb8970c7c3593114e` |
| Latest merged theorem PR | #4773 |
| #4773 validated exact head | `5325474e940e57b54b4e00d85a30c519f58cdca4` |
| #4773 CI | PR Lean Fast Check #15126 / run 36145120296 — success |
| #4773 completion receipt | `chatgpt-ci-receipt/PR Lean Fast Check` — success |
| Lean | v4.30.0-rc2 |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Default branch | `main` — not theorem authority |

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A later docs-only merge may advance the theorem-carrier pointer without changing the theorem-bearing mathematical baseline above.

## Proof spine at a glance

~~~text
FINITE WILSON / OS / PHYSICAL TRANSFER ROOT
  -> periodic SU(N) Wilson one-slab kernel
  -> OS / Gauss-law physical carrier
  -> compact positive physical transfer
  -> canonical nonnegative vacuum
  -> ground-state transformed boundary and joint laws
  -> genuine one-link / six-color conditional expectations

EXACT BETA-ZERO ENDPOINT
  -> vacuum = spatial Haar
  -> ground-state joint law = pair Haar
  -> kappa_0 = 1/6
  -> q_0 = 5/6
  -> exact physical transfer gap = 1

POSITIVE-BETA PHYSICAL RESPONSE / MATRIX SIDE
  -> fixed-right response continuity and canonical response profile
  -> physical influence / resolvent propagation
  -> covariance decay and shell summability
  -> background-dependent physical envelope K_A
  -> volume-independent row + column Schur coefficient q_phys(s,beta) < 1
  -> transpose one-sided Schur receiver

SWEEP LOCAL ENERGY
  -> ordered same-color one-link path loss
  -> six-spatial link-indexed stage profile ell_s
  -> (1/6) sum_s ell_s^2 <= E_6sp

GENUINE localPart BRIDGE                          #4738-#4770
  -> kernel-section local-mean L2 carrier
  -> exact joint = vacuum tensor_m kernel-section disintegration
  -> canonical split one-link Markov kernel and measurable fiber mean
  -> canonical fiber variance <= genuine CondExpL2 residual^2
  -> canonical mean = diagonal remote kernel-section projection
  -> canonical residual = diagonal remote fluctuation over the whole target fiber
  -> vacuum / kernel-section a.e. descent
  -> canonical variance = vacuum average of diagonal section L2 norm^2
  -> genuine-joint canonical residual L2 vector
  -> real norm bound by exact one-link CondExp residual
  -> canonical sweep-prefix representative
  -> ||localPart_s|| <= ell_s with coefficient 1

RESPONSE / OUTER SCHUR BRIDGES                    #4771-#4773
  -> source-specific pair/background L2 response carrier
  -> pointwise a.e. response bound lifts to L2 norm with coefficient 1
  -> physical K_A <= configuration-independent canonical pin-free kernel
  -> full-envelope centered RMS upgrades to canonical pin-free coefficient
  -> background-dependent one-sided Schur inequality integrates over arbitrary outer law
  -> physical-vacuum specialization
  -> transpose outer-lintegral Schur receiver

CURRENT FRONTIER
  -> construct the actual observable-specific response / state decomposition
     or equivalent pointwise outer-background transpose recurrence
  -> preserve K(target,source), never K(source,target)
  -> place the already-closed localPart energy in the same recurrence
  -> apply #4773 (or the #4723 dependent-carrier route)
  -> close positive-beta bounded-core six-spatial Poincare
  -> #4650 full genuine joint L2
  -> #4651 q(beta) < 1 and finite-volume physical transfer gap
  -> thermodynamic / infinite-volume construction
  -> OS / Wightman continuum construction
  -> continuum Yang--Mills mass gap
~~~

## What changed after PR #4761

The previous documentation stopped immediately after identifying the canonical fiber mean with the diagonal remote projection. That was no longer the actual frontier.

### #4764--#4767 — finish the exact integrated localPart energy glue

PR #4764 extends the #4761 residual identity from the identity-inserted target representative to **every value of the target fiber**, using off-target invariance of the direct one-link law and of the diagonal remote projection.

PR #4765 rewrites the canonical fiber variance exactly as split-coordinate diagonal fluctuation energy.

PR #4766 transports that identity through the target/off-target measurable equivalence and descends it first from Haar to the literal kernel-section law and then from Haar to the physical vacuum law.

PR #4767 then inserts that a.e. identity into the canonical variance representation and proves the exact energy identity

~~~text
CanonicalFiberVarianceFunctional
  =
vacuum-average_C
  ||diagonalLocalMeanKernelSectionL2(C)||^2.
~~~

Combining this with the already-established canonical variance bound gives the coefficient-one integrated localPart energy estimate.

### #4768--#4770 — package the localPart vector and close the stage-profile bound

PR #4768 packages the canonical fiber-mean centered residual as an actual vector in the genuine ground-state joint L2 space and identifies its squared norm with the canonical fiber variance.

PR #4769 removes the ENNReal / square wrapper and proves the real norm estimate required by the response assembler:

~~~text
||canonicalResidualL2||
  <=
||stageVector - P_e stageVector||.
~~~

PR #4770 proves the finite-list bridge from the exact residual at the occurrence of a link in the canonical sweep to the existing sweep-stage amplitude. Therefore, for every genuine spatial link,

~~~text
||localPart_s|| <= ell_s.
~~~

This closes the former localPart frontier with coefficient one and no volume-dependent factor.

## Response-side infrastructure now available

### #4771 — source-specific L2 response carrier

The source-specific pair/background law from #4724 is used as the dependent carrier

~~~text
E_s = L2(nu_s).
~~~

A concrete response with a `MemLp 2` certificate can be packaged in `E_s`. If almost everywhere

~~~text
|R_{s,t}| <= K(t,s) * amplitude_t,
~~~

then the same coefficient survives at the L2 norm level:

~~~text
||R_{s,t}|| <= K(t,s) * amplitude_t.
~~~

No extra Cauchy or cardinality factor is introduced.

### #4772 — configuration-independent canonical pin-free RMS envelope

The actual background-dependent physical envelope is bounded pointwise by the configuration-independent pin-free kernel generated from the canonical fixed-right response profile:

~~~text
K_A(target,source) <= K_pinfree(target,source).
~~~

The existing full-envelope centered RMS theorem therefore upgrades to the same canonical pin-free coefficient while preserving the exact target/source orientation.

### #4773 — integrate the actual background-dependent Schur theorem

PR #4773 takes a complementary route: instead of forcing `K_A` outside the outer integral, it keeps the actual background-dependent matrix and applies the already-proved Schur inequality pointwise in `A`.

It proves arbitrary-outer-measure and physical-vacuum versions of both orientations:

~~~text
profile_A(target)
  <= local_A(target)
     + sum_source K_A(target,source) profile_A(source)

and

profile_A(source)
  <= local_A(source)
     + sum_target K_A(target,source) profile_A(target).
~~~

The same volume-independent scalar coefficient

~~~text
q_phys(s,beta) < 1
~~~

survives outer `lintegral` unchanged.

This removes the need to replace the physical envelope by a coarser matrix merely to integrate the Schur estimate.

## Current mathematical frontier

The localPart theorem is no longer open. The Schur matrix theorem is no longer open. The outer-integration theorem is no longer open.

The remaining finite-volume positive-beta task is to build the **actual observable-specific recurrence** in one of the now-available equivalent interfaces.

### Route A — dependent source-carrier assembler

Instantiate PR #4723 with source-specific carriers and actual vectors:

~~~text
state_s
  = localPart_s + sum_t R_{s,t}

||localPart_s|| <= ell_s                    -- closed by #4770

||R_{s,t}||
  <= K(t,s) ||state_t||.                    -- concrete instantiation still open
~~~

PR #4771 supplies the coefficient-preserving L2 lift and PR #4772 supplies a configuration-independent canonical physical coefficient when that presentation is useful.

### Route B — outer-background scalar recurrence

Construct physical profile fields `profile A e` and `localProfile A e` satisfying pointwise in the outer background

~~~text
profile A source
  <= localProfile A source
     + sum_target K_A(target,source) * profile A target.
~~~

Then PR #4773 immediately integrates the transpose Schur coercivity over the physical vacuum law.

This route preserves the actual background-dependent physical kernel throughout.

### Next downstream target

Whichever interface is used, the next closed theorem should feed the observable-specific recurrence into the already-proved local-energy normalization and produce a volume-independent bounded-core six-spatial Poincare inequality.

After that:

~~~text
bounded-core positive-beta Poincare
  -> #4650 full genuine joint L2 closure
  -> #4651 six-spatial Rayleigh q(beta) < 1
  -> positive-beta finite-volume physical transfer gap
  -> thermodynamic / infinite-volume limit
  -> continuum OS / Wightman reconstruction
  -> continuum mass gap
~~~

## Recent theorem units

| PR | Role | Merge commit |
| --- | --- | --- |
| #4764 | lift canonical residual identity across the whole target fiber | `768cb059cfed2847cd912abd614f23468dc6137d` |
| #4765 | canonical variance = split diagonal fluctuation energy | `010fc4e6e6a964c65649b8838588269c39c6ae2c` |
| #4766 | descend residual identity to vacuum / kernel-section laws | `7fcfcd38f27904c868d11dfd8bfe829e56eeacba` |
| #4767 | canonical variance = vacuum diagonal section L2 energy | `7bd02830473645ac76d2a6dd43bb5a5c11fc847f` |
| #4768 | package canonical residual in genuine joint L2 | `42a01e847a4da1099509eaf21fda243cd09f6c89` |
| #4769 | convert canonical residual energy to real sweep-stage norm | `f6334b1aa5b0e540dbd9ff02c780e0b0c2a58657` |
| #4770 | prove canonical sweep localPart norm <= stage profile | `b12ec21f58c06e036cc2b81cc655706cdb71ffa0` |
| #4771 | lift source-pair responses into dependent L2 carrier | `0d6351704115da08e093417297e50506bcf61028` |
| #4772 | upgrade full-envelope RMS to canonical pin-free kernel | `d92764b7cf374187fddad50080bad44af05ff0df` |
| #4773 | integrate background-dependent row + transpose Schur coercivity | `e4c878398f0d0aa183cfc86eb8970c7c3593114e` |

PR #4762 remains closed / unmerged and is not theorem authority.

## Lean / mathlib engineering discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Current rules:

- fresh theorem-carrier and recent PR observation before branch creation, write, CI judgment, and merge judgment;
- use the PR's current exact `head_sha`; never classify CI from a stale workflow SHA;
- inspect the whole changed Lean file, CompileSmoke, imports, dependent theorem signatures, and pinned API when CI is red;
- distinguish preflight/import failures from actual Lean elaboration failures;
- import the actual defining local module when the static dependency audit requires it;
- inspect the **Changed Lean fast check** step itself and the exact-head completion receipt;
- theorem proofs establishing `IsProbabilityMeasure` / `IsMarkovKernel` are not automatically installed instances; use local `letI` when downstream APIs need them;
- avoid broad reverse `rw` across dependent measures / Lp carriers;
- prefer typed intermediate proof terms and narrow `simpa only [...] using ...`;
- `simp at h` mutates a hypothesis; `simpa using h` closes the current goal — do not write nonexistent `simpa ... at h` syntax;
- choose the correct measurable-equivalence identity direction, e.g. `symm_apply_apply` versus `apply_symm_apply`;
- preserve the exact response orientation `K(target,source)`;
- treat pinned mathlib as authority; current master is only a syntax/API reference;
- do not pointwise evaluate arbitrary L2 quotient representatives.

## Status summary

~~~text
finite Wilson / OS / physical-transfer root         CLOSED
exact beta-zero endpoint                            CLOSED
positive-beta physical matrix / Schur side          CLOSED
six-spatial sweep local energy                      CLOSED
link-indexed stage profile ell_s                    CLOSED
kernel-section / genuine-joint disintegration       CLOSED
canonical one-link variance bridge                  CLOSED
integrated localPart energy glue                    CLOSED
genuine-joint localPart L2 vector                   CLOSED
||localPart_s|| <= ell_s                             CLOSED
source-specific response L2 lift                    CLOSED (generic)
canonical pin-free full-envelope RMS                CLOSED
outer row + transpose Schur integration             CLOSED

actual observable-specific response decomposition   OPEN
concrete recurrence / receiver instantiation         OPEN
positive-beta bounded-core Poincare                 OPEN
full-L2 positive-beta finite-volume gap             OPEN
thermodynamic / continuum mass gap                  OPEN
~~~

## Navigation

- `ROADMAP.md` — detailed restart point and theorem sequence.
- `MGAP4D/MathlibAnalytic` — formal analytic development.
- theorem-carrier branch — `formal/real-hilbert-uniform-coercive-strong-limit`.
