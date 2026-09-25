# MGAP4D

MGAP4D is Hidetoshi Itakura's Lean 4 / mathlib program for a proof-carrying construction of four-dimensional Yang--Mills theory.  The repository develops a finite-volume periodic Wilson / Osterwalder--Schrader / physical-transfer framework, exact beta-zero geometry, positive-beta physical response and covariance control, genuine ground-state conditional expectations, Hilbert-space coercivity receivers, and downstream thermodynamic / continuum infrastructure.

## Current status — 2026-09-25 JST

The unique authoritative theorem-carrier branch is:

**`formal/real-hilbert-uniform-coercive-strong-limit`**

The fresh theorem-bearing baseline immediately before this documentation refresh is:

**`6bd73357bd0aa4d358923806e648a04300253e4c`**

This is the merge commit of PR **#4761**, **Identify canonical fiber mean with diagonal remote projection**.

The default branch **`main` is not theorem authority**.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> What is integrated is a substantial finite-volume Wilson / OS / physical-transfer theorem spine.  The exact beta-zero endpoint is closed.  The positive-beta physical influence matrix has a volume-independent bidirectional Schur coefficient.  The genuine six-spatial sweep local-energy receiver is closed.  The current work is closing the observable-specific positive-beta localPart / response recurrence on the genuine joint law.
>
> Since PRs #4738--#4761, the former localPart obstruction has been reduced to one final measure/integration glue: the canonical genuine one-link centered residual is now identified almost everywhere with the same diagonal remote kernel-section fluctuation whose section conditional-square energy was proved in #4749 to equal the squared norm of the canonical section L2 carrier.

## Repository authority

| Item | Current value |
| --- | --- |
| Theorem-carrier branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Theorem-bearing baseline before this docs refresh | `6bd73357bd0aa4d358923806e648a04300253e4c` |
| Latest merged theorem PR | #4761 |
| #4761 validated exact head | `15037f06f3efd4fae70cbc2d5fdd96d21db036ae` |
| #4761 CI | PR Lean Fast Check #15098 / run 36105350621 — success |
| #4761 completion receipt | `chatgpt-ci-receipt/PR Lean Fast Check` — success |
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

HIGH-TEMPERATURE PHYSICAL RESPONSE / INFLUENCE
  -> fixed-right response continuity
  -> physical influence / resolvent propagation
  -> covariance decay and shell summability
  -> volume-independent strict physical sweep interval

GENUINE GROUND-STATE L2 RECEIVERS
  -> bounded-concrete -> full joint L2 closure
  -> six-spatial frame / random-scan Rayleigh receiver
  -> physical transfer-gap receiver

EXACT BETA-ZERO ENDPOINT
  -> physical transfer gap = 1
  -> vacuum = spatial Haar
  -> joint law = pair Haar
  -> kappa_0 = 1/6, q_0 = 5/6
  -> six-spatial consistency bound gap >= 1/16

POSITIVE-BETA MATRIX / SCHUR SIDE
  -> actual physical envelope K
  -> row + column control by q_phys < 1
  -> transpose one-sided Schur recurrence receiver

SWEEP LOCAL ENERGY
  -> ordered path loss <= six-spatial residual energy
  -> link-indexed local profile ell_s
  -> (1/6) sum_s ell_s^2 <= E_6sp

SOURCE-DEPENDENT ASSEMBLER
  -> #4723 accepts source-specific normed carriers E_s
  -> state_s = localPart_s + sum_t response_{s,t}
  -> ||localPart_s|| <= ell_s
  -> ||response_{s,t}|| <= K_{t,s} ||state_t||

LOCALPART GENUINE-LAW BRIDGE                       #4738-#4761
  -> section local-mean L2 carrier
  -> fluctuation-sector placement
  -> exact joint = vacuum ⊗ kernel-section disintegration
  -> genuine split fiber = kernel-section one-link law
  -> diagonal section carrier
  -> section conditional-square energy = ||r_C^KS||^2
  -> canonical genuine split Markov kernel + measurable fiber mean
  -> canonical fiber variance <= genuine CondExpL2 residual norm^2
  -> genuine joint / kernel-section Fubini
  -> canonical mean = kernel-section one-link integral
  -> diagonal reference one-link fiber = kernel-section law
  -> diagonal remote projection = same kernel-section integral
  -> canonical genuine residual = diagonal remote kernel-section fluctuation a.e.

CURRENT FRONTIER
  -> integrate the #4761 residual identification through the exact
     vacuum / off-target / target coordinate decomposition
  -> identify the resulting energy with the #4749 vacuum-averaged
     diagonal section norm^2
  -> package the source-specific localPart carrier with coefficient 1:
       ||localPart_s|| <= ell_s
  -> independently prove lawResponse:
       ||R_{s,t}|| <= K_{t,s} ||x_t||
     with the transpose orientation preserved
  -> feed both into #4723
  -> #4713 transpose recurrence
  -> #4687 + #4691 uniform Schur coercivity
  -> bounded-core six-spatial Poincare
  -> #4650 full genuine joint L2
  -> #4651 positive-beta physical transfer gap
  -> thermodynamic / continuum OS-Wightman construction
~~~

## The localPart bridge: what is now closed

### #4738--#4749: section carrier and exact section energy

The fixed-right local mean was first realized as a genuine section-space L2 vector.  The diagonal specialization then produced a canonical carrier

~~~text
r_C^KS in L2(kappa_C)
~~~

and #4749 proved the exact identity

~~~text
int_A [ int_D q_C(D)^2 K_link(A,dD) ] kappa_C(dA)
  = ||r_C^KS||^2.
~~~

No comparison constant is present.

### #4740--#4747: exact joint / section law compatibility

The continuous fixed-right kernel-section density was packaged as an explicit Markov kernel.  The genuine joint law was then disintegrated exactly as

~~~text
mu_joint = mu_vacuum tensor_m kappa_section.
~~~

The genuine one-link split fiber was also identified with the kernel-section one-link normalized law after target-coordinate evaluation.

### #4750--#4757: canonical genuine fiber variance

A single integrand-independent canonical split Markov kernel and measurable canonical fiber mean were fixed.

The following chain is now formalized:

~~~text
canonical fiber mean
  -> exact evariance / centered-residual identity
  -> canonical weighted fiber variance
  -> coefficient-one bound by genuine one-link centered residual
  -> exact centered residual = global CondExpL2 residual norm^2
  -> joint/kernel-section lintegral disintegration
  -> vacuum/kernel-section residual presentation.
~~~

Thus the canonical fiber variance is already bounded by the genuine one-link CondExpL2 residual with coefficient one.

### #4758--#4761: identify the residual itself with the diagonal section fluctuation

#4758 identifies the canonical genuine fiber mean almost everywhere with the literal one-link kernel-section integral.

#4759 identifies the diagonal reference one-link fiber with the kernel-section one-link law.

#4760 identifies the diagonal remote heat-bath projection pointwise with that same kernel-section integral.

#4761 therefore proves, almost everywhere in retained outer coordinates,

~~~text
canonical genuine fiber mean
  = diagonal remote kernel-section projection
~~~

and consequently

~~~text
F(left,right_from_retained) - canonical_mean
  = diagonal remote kernel-section fluctuation.
~~~

This is the key identity needed to glue #4757 back to #4749.

## Immediate remaining localPart theorem

The next theorem unit should not introduce a new estimate.  It should perform the exact measure-theoretic glue:

1. use #4761 to replace the canonical centered residual by the diagonal remote fluctuation;
2. use the target/off-target measurable coordinate equivalence and the exact one-link law identifications;
3. use #4756 / #4757 to move between genuine joint and vacuum/kernel-section integration;
4. use #4749 to replace the section conditional-square energy by `||r_C^KS||^2`;
5. package the outer-vacuum RMS carrier required by #4723;
6. conclude the coefficient-one bound
   `||localPart_s|| <= ell_s`.

The pointwise statement `||r_C^KS|| <= ell_s` is neither required nor the intended route.

## Independent remaining lawResponse obligation

The response side remains separate from localPart.

For source `s` and target `t`, the required assembler estimate is

~~~text
||R_{s,t}|| <= K_{t,s} ||x_t||.
~~~

The transpose orientation is essential.  Existing response theorems must be checked by their signatures, not by names; a naive application can produce `K_{s,t}` instead.

Do not mix this step into the localPart energy glue.

## Assembler and downstream chain

Once the two source-specific estimates are available,

~~~text
x_s = localPart_s + sum_t R_{s,t}

||localPart_s|| <= ell_s

||R_{s,t}|| <= K_{t,s} ||x_t||
~~~

#4723 gives the exact source-dependent one-sided recurrence, #4713 closes the transpose recurrence, and #4687 / #4691 supply the volume-independent Schur coercivity receiver.

The intended downstream chain remains:

~~~text
localPart + lawResponse
  -> #4723 source-dependent assembler
  -> #4713 transpose recurrence
  -> #4687 + #4691 uniform Schur coercivity
  -> bounded-core six-spatial Poincare
  -> #4650 full genuine joint L2
  -> #4651 six-spatial Rayleigh q(beta) < 1
  -> positive-beta finite-volume physical transfer gap
  -> thermodynamic / infinite-volume limit
  -> OS / Wightman continuum construction
  -> continuum Yang--Mills mass gap
~~~

## Recent theorem units

| PR | Role | Merge commit |
| --- | --- | --- |
| #4738 | local-mean kernel-section L2 carrier | pre-#4739 baseline |
| #4739 | local-mean carrier in fluctuation sector | `8720285a644d3c4aea9634ce7a3a7af0a5816dbb` |
| #4740 | measurable fixed-right kernel-section Fubini bridge | `cb6615d51807a3a09e229f50870dc1ad4a87139b` |
| #4741 | genuine joint density factorization | `b2d8b7d2cb79ea8c7c3ac5bac1295a96094f4bdb` |
| #4742 | fixed-left orientation | `73683c70fd7788ac39de0bdfe927ed9c9aefd0a8` |
| #4743 | weighted kernel-section Fubini | merged |
| #4744 | physical measure presentation | merged |
| #4745 | explicit kernel-section Markov kernel | `9536aa310f849c6e4dbdc4fe9cd6db14f842e23c` |
| #4746 | exact joint-law disintegration | `f53b58bee9ef3678eecd90be33e1d6adbc951ffc` |
| #4747 | genuine one-link fiber = kernel-section fiber | `c9253c3546c35d717209403919ddbd26a189c6fa` |
| #4748 | diagonal section L2 carrier | `cfcb224b26aaf3dad280e2f655729bb7652554f2` |
| #4749 | diagonal section conditional-square energy = norm² | `ddb0ede53028d49c4f27e7a2c20c4c242fdf556b` |
| #4750 | canonical split Markov kernel + fiber mean | `4c67a6166d02f0f555968bbab2470c2f77981915` |
| #4751 | canonical split-kernel integral identity | `bf4fd8a43eaa64d398928a00dc1c71d3642459d7` |
| #4752 | canonical fiber-mean variance minimality | `b5a049b005ce65446ed67b06ac79232b36a3416a` |
| #4753 | integrate canonical fiber variance below centered residual | `f1283f7b5720e87133685e016721592257e1429c` |
| #4754 | canonical fiber variance <= genuine CondExpL2 residual² | `37f89cb4b07fee26f2ee241e094ae14c0c62d251` |
| #4755 | canonical fiber variance = canonical centered residual | `f874d7be6ac9d889f71738bf4b50e312aae9d336` |
| #4756 | genuine joint kernel-section lintegral disintegration | `47b17b27722d6a4cd103a04143cafbdae782df9a` |
| #4757 | canonical variance in kernel-section residual coordinates | `cd62b7087cee27e4bf55efa7330043e92a2c2860` |
| #4758 | canonical fiber mean = kernel-section one-link integral | `7e842185bda3d8230dd4437217f1f33109a76bc2` |
| #4759 | diagonal reference fiber = kernel-section one-link law | `436a1b0ec53182ee7262605368a408b53dc5f240` |
| #4760 | diagonal remote projection = kernel-section integral | `0c977c5f346cd661072b5dc52a36b2a7037b6894` |
| #4761 | canonical mean = diagonal remote projection; residual = fluctuation | `6bd73357bd0aa4d358923806e648a04300253e4c` |

PR #4762 is **closed / unmerged** and is not theorem authority.

## Lean / mathlib engineering discipline

Pinned environment:

- Lean v4.30.0-rc2
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Current rules:

- fresh theorem-carrier and recent PR observation before branch creation, write, CI judgment, and merge judgment;
- use the PR's current exact `head_sha`; never classify CI from a stale workflow SHA;
- inspect the whole changed Lean file, CompileSmoke, imports, dependent theorem signatures, and pinned API when CI is red;
- inspect the **Changed Lean fast check** step itself and the exact-head completion receipt;
- treat theorem proofs establishing `IsProbabilityMeasure` / `IsMarkovKernel` as propositions, not automatically installed instances; introduce local `letI` when downstream APIs require `SFinite` / `IsSFiniteKernel`;
- keep dependent measure equalities narrow; avoid broad reverse `rw` over dependent carriers;
- prefer constructing a typed proof term and then `simpa only [h] using hBase`;
- preserve the exact source/target orientation in response estimates;
- treat the pinned mathlib revision as authority; current master is only a reference;
- do not pointwise evaluate arbitrary L2 quotient representatives.

## Status summary

~~~text
matrix / Schur side                                CLOSED
six-spatial sweep local energy                     CLOSED
link-indexed local profile ell_s                   CLOSED
source-dependent assembler receiver                CLOSED
bounded-concrete / genuine CondExp infrastructure  CLOSED
kernel-section / genuine joint disintegration      CLOSED
canonical one-link fiber variance bridge           CLOSED
canonical mean = diagonal remote projection        CLOSED
canonical residual = diagonal remote fluctuation   CLOSED

final integrated localPart energy glue             OPEN
localPart carrier norm <= ell_s                     OPEN
lawResponse K_{t,s} ||x_t|| bound                  OPEN
assembler instantiation / transpose recurrence      OPEN
positive-beta bounded-core Poincare                OPEN
full-L2 positive-beta gap                          OPEN
thermodynamic / continuum mass gap                 OPEN
~~~

## Navigation

- `ROADMAP.md` — detailed restart point and theorem sequence.
- `MGAP4D/MathlibAnalytic` — formal analytic development.
- theorem-carrier branch — `formal/real-hilbert-uniform-coercive-strong-limit`.
