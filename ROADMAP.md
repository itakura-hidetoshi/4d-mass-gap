# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-25 JST

Repository:

**`itakura-hidetoshi/4d-mass-gap`**

Unique authoritative theorem-carrier branch:

**`formal/real-hilbert-uniform-coercive-strong-limit`**

Fresh theorem-bearing baseline immediately before this documentation refresh:

**`6bd73357bd0aa4d358923806e648a04300253e4c`**

This is the merge commit of PR **#4761**, **Identify canonical fiber mean with diagonal remote projection**.

The default branch **`main` is not theorem authority**.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A docs-only merge may advance the theorem-carrier pointer without changing the theorem-bearing mathematical baseline above.

---

## 0. Claim boundary

The repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

What is currently integrated includes:

- finite-volume periodic Wilson / OS / physical-transfer construction;
- canonical nonnegative vacuum and ground-state transform;
- high-temperature physical response / influence / covariance machinery;
- exact beta-zero physical endpoint;
- genuine one-link and six-spatial conditional-expectation infrastructure;
- positive-beta bidirectional physical Schur control;
- link-indexed sweep-stage local-energy profile;
- source-dependent normed response assembler;
- exact genuine-joint / kernel-section disintegration;
- canonical genuine one-link fiber variance and coefficient-one comparison with the global one-link CondExpL2 residual;
- identification of the canonical fiber mean with the diagonal remote kernel-section projection;
- identification of the corresponding canonical centered residual with the diagonal remote kernel-section fluctuation.

The immediate obstruction is no longer the existence of a measurable canonical fiber center.  It is the final exact integration glue from the #4761 fluctuation identity to the #4749 diagonal section L2 norm identity, followed by packaging the resulting coefficient-one localPart carrier for #4723.

The independent response-side obstruction remains the transpose-oriented estimate

~~~text
||R_{s,t}|| <= K_{t,s} ||x_t||.
~~~

---

## 1. Pinned formal environment

Lean:

**v4.30.0-rc2**

mathlib:

**`5450b53e5ddc75d46418fabb605edbf36bd0beb6`**

Do not use current mathlib master as theorem authority.

When CI is red, inspect:

- the exact error line;
- the full changed Lean module;
- CompileSmoke;
- the complete import closure;
- dependent theorem signatures;
- the pinned mathlib API;
- typeclass and elaboration structure.

Merge judgment requires the PR's current exact head, terminal success of **Changed Lean fast check**, and a success exact-head completion receipt.

---

## 2. Stable downstream receiver spine

The following layers are already available and should not be rebuilt.

### 2.1 Genuine ground-state L2 / transfer receiver

PRs #4650--#4652 supply:

- bounded-concrete -> full genuine joint L2 closure;
- six-spatial residual / Rayleigh receivers;
- physical transfer-gap receiver;
- finite Hilbert projection infrastructure.

### 2.2 Exact beta-zero endpoint

PRs #4653--#4682 close the beta-zero endpoint:

~~~text
vacuum measure = spatial Haar
ground-state joint measure = pair Haar
kappa_0 = 1/6
q_0 = 5/6
six-spatial consistency bound gap >= 1/16
exact physical transfer gap = 1
~~~

The 1/16 bound is a consistency receipt, not the exact beta-zero gap.

### 2.3 Positive-beta physical Schur side

PRs #4683--#4687 close the actual physical envelope / matrix side.

For the physical influence envelope `K` there is a volume-independent strict coefficient

~~~text
0 <= q_phys(s,beta) < 1
~~~

with both row and column control.

The transpose recurrence receiver accepts

~~~text
u_s <= ell_s + sum_t K_{t,s} u_t
~~~

and yields the uniform L2 Schur estimate.

### 2.4 Sweep local energy

PRs #4688--#4690 provide the canonical sweep-stage local profile `ell_s` with

~~~text
(1/6) * sum_s ell_s^2
  <= E_6sp.
~~~

### 2.5 Source-dependent assembler

PR #4723 already accepts source-specific normed carriers `E_s`.

Its intended inputs are

~~~text
x_s = localPart_s + sum_t R_{s,t}

||localPart_s|| <= ell_s

||R_{s,t}|| <= K_{t,s} ||x_t||.
~~~

This is the receiver to target.  Do not collapse source/target indices or replace it with a same-carrier approximation.

---

## 3. localPart bridge — section-space construction

### #4738 — local-mean section L2 carrier

The physical source-update local mean is realized as an actual vector in the fixed-right kernel-section L2 space.

The exact norm-square identity is formalized at section level.

### #4739 — fluctuation sector

The local-mean carrier is placed in the source one-link fluctuation sector.

The projection onto the corresponding off-fiber conditional subspace is exactly zero.

### #4748 — diagonal section carrier

For an outer boundary `C`, set the auxiliary background and current values diagonally:

~~~text
B = C
left = C
k = C distinguishedSource
g2 = C link.
~~~

The dependent Lp cast is avoided by constructing the diagonal vector directly from the specialized `MemLp 2` theorem.

This yields the canonical section vector

~~~text
r_C^KS in L2(kappa_C).
~~~

### #4749 — diagonal conditional-square energy

The section fluctuation

~~~text
q_C(A)
~~~

satisfies the exact identity

~~~text
int_A [ int_D q_C(D)^2 K_link(A,dD) ] kappa_C(dA)
  = ||r_C^KS||^2.
~~~

No comparison coefficient appears.

**Status: closed sectionwise.**

---

## 4. genuine joint / kernel-section disintegration

### #4740--#4745 — measurable section kernel

The fixed-right section weight is exposed as a jointly measurable normalized kernel.

The section mass is exactly the transfer eigenvalue times the continuous vacuum representative.

An explicit Markov kernel

~~~text
kappa_section(C,dA)
~~~

is constructed, with each fiber equal to the literal normalized fixed-right kernel-section law.

### #4746 — exact measure disintegration

The genuine two-boundary ground-state law is exactly

~~~text
mu_joint = mu_vacuum tensor_m kappa_section.
~~~

This is integrand-independent.

### #4747 — genuine split one-link fiber compatibility

After target-coordinate evaluation, the historical genuine split target fiber agrees almost everywhere with the kernel-section one-link normalized law.

**Status: closed.**

---

## 5. canonical genuine split kernel and fiber mean

### #4750 — fixed canonical split Markov kernel

Choose once, independently of the observable, the Markov kernel supplied by the genuine split disintegration.

Define the canonical fiber mean

~~~text
m_F(left,retained)
  = integral F(left,reconstruct(targetCfg,retained)) d kappa_canonical.
~~~

The center is strongly measurable in the retained outer context.

### #4751 — canonical split Fubini

The historical split Fubini identity is upgraded from an existential witness kernel to the fixed canonical kernel.

### #4752 — fiberwise variance minimality

The centered residual around the canonical mean is exactly Mathlib's `evariance` and is no larger than the residual around any other scalar center.

### #4753 — integrate variance below centered residual

The canonical fiber variance is integrated against the exact outer-context mass and bounded with coefficient one by the genuine one-link centered-residual functional.

### #4754 — global CondExpL2 bound

The centered-residual functional is identified with the squared norm of the genuine global one-link conditional-expectation residual, giving

~~~text
CanonicalFiberVarianceFunctional
  <= ENNReal.ofReal ||f - P_target f||^2.
~~~

### #4755 — exact canonical-centered presentation

When the center is the canonical fiber mean,

~~~text
CanonicalFiberVarianceFunctional
  = CenteredResidualFunctional(canonical mean).
~~~

### #4756 — joint/kernel-section lintegral interface

For nonnegative measurable `Phi`,

~~~text
integral_{mu_joint} Phi
  = integral_C integral_A Phi(C,A) d kappa_C(A) d mu_vacuum(C).
~~~

This packages #4746 into the exact Fubini interface needed by the localPart bridge.

### #4757 — canonical residual in kernel-section coordinates

The same canonical variance is expressed exactly as a physical-vacuum average of the canonical-mean squared residual under the literal fixed-right kernel-section laws.

The coefficient-one `CondExpL2` residual bound is retained in this presentation.

**Status: closed.**

---

## 6. identify the canonical center with the diagonal remote projection

### #4758 — canonical fiber mean = kernel-section one-link integral

Almost everywhere in retained outer coordinates, the canonical genuine fiber mean is the literal kernel-section one-link expectation of the concrete section.

### #4759 — diagonal reference fiber = kernel-section law

The diagonal reference one-link fiber appearing in the remote heat-bath construction is identified with the same fixed-right kernel-section one-link normalized law.

### #4760 — diagonal remote projection = kernel-section integral

The existing remote one-link projection is identified pointwise with that same kernel-section one-link integral.

### #4761 — canonical fiber mean = diagonal remote projection

Combining #4758 and #4760 gives, almost everywhere in retained outer coordinates,

~~~text
canonical genuine fiber mean
  = diagonal remote kernel-section projection.
~~~

Therefore

~~~text
F(left,right_from_retained) - canonical mean
  = diagonal remote kernel-section fluctuation.
~~~

This is precisely the fluctuation used by #4748--#4749.

Validated exact head:

**`15037f06f3efd4fae70cbc2d5fdd96d21db036ae`**

CI:

**PR Lean Fast Check #15098 / run 36105350621 — success**

Exact-head completion receipt:

**success**

Merge commit:

**`6bd73357bd0aa4d358923806e648a04300253e4c`**

PR #4762 is closed / unmerged and is not authority.

---

## 7. Immediate theorem frontier — finish coefficient-one localPart energy glue

This is the next mathematical unit.

The goal is **not** to prove a pointwise bound

~~~text
||r_C^KS|| <= ell_s.
~~~

That stronger statement is unnecessary and is not the intended route.

The correct route is integrated.

### 7.1 Starting identities

From #4757:

~~~text
CanonicalFiberVarianceFunctional
  = vacuum average of canonical centered residual energy.
~~~

From #4761:

~~~text
canonical centered residual
  = diagonal remote kernel-section fluctuation
~~~

almost everywhere in the retained outer coordinates.

From #4749:

~~~text
section conditional-square energy
  = ||r_C^KS||^2.
~~~

### 7.2 Required glue

Use the exact target/off-target coordinate splitting, the kernel-section one-link law identities, and the vacuum/kernel-section Fubini theorem to identify the same energy on both sides.

The desired intermediate statement is schematically

~~~text
vacuum-average_C ||r_C^KS||^2
  = CanonicalFiberVarianceFunctional
~~~

or an equivalent exact ENNReal / real-energy formulation.

Then #4754 immediately gives

~~~text
vacuum-average_C ||r_C^KS||^2
  <= ||f - P_s f||^2.
~~~

The right-hand side is the genuine one-link residual amplitude underlying the canonical sweep local profile `ell_s`.

### 7.3 Package the source-specific localPart carrier

After the energy identity, construct the source-specific normed carrier required by #4723.

Acceptable implementations include:

- a genuine outer-vacuum L2 field of section vectors, if measurability is cleanly available; or
- an equivalent canonical normed/RMS carrier whose norm square is definitionally or theoremically the integrated section energy.

The required final interface is

~~~text
||localPart_s|| <= ell_s.
~~~

No additional comparison factor is allowed.

**Status: open; all law-identification ingredients are now present.**

---

## 8. Independent theorem frontier — lawResponse

The response term is separate.

For source `s` and target `t`, prove in the same source-specific carrier:

~~~text
||R_{s,t}||
  <= K_{t,s} ||x_t||.
~~~

### Orientation rule

The required matrix entry is

~~~text
K_{t,s},
~~~

not `K_{s,t}`.

The transpose orientation established around #4715 / #4723 must be preserved.

Do not infer orientation from theorem names; inspect exact signatures.

### Scope rule

Do not mix lawResponse into the remaining localPart integration proof.

**Status: open.**

---

## 9. Assemble the recurrence

Once Sections 7 and 8 are closed, instantiate #4723 with

~~~text
x_s
localPart_s
R_{s,t}.
~~~

Obtain

~~~text
||x_s||
  <= ell_s + sum_t K_{t,s} ||x_t||.
~~~

Then use #4713 and the #4687 / #4691 Schur receiver.

**Status: receiver closed; concrete instantiation open.**

---

## 10. Positive-beta bounded-core Poincare target

After the source-dependent recurrence closes,

~~~text
(1/6) * (1-q_phys)^2 * sum_s ||x_s||^2
  <= E_6sp.
~~~

Combine this with the appropriate global profile / centered-energy majorant to obtain a bounded-core Poincare inequality with volume-independent coefficient.

Do not freeze the final numerical coefficient until the actual carrier normalization and global majorant are connected.

**Status: open.**

---

## 11. Full genuine joint L2 and finite-volume physical gap

After bounded-core Poincare:

1. apply #4650 to extend to full genuine joint L2;
2. use #4651 to obtain six-spatial Rayleigh `q(beta) < 1`;
3. apply the physical transfer-gap receiver;
4. obtain a finite-volume gap lower bound independent of volume on the certified positive-beta interval;
5. transport to the exact Hamiltonian normalization and vacuum-orthogonal sector.

**Status: downstream.**

---

## 12. Thermodynamic / infinite-volume construction

Required later:

- compatible finite-volume embeddings / restrictions;
- consistency of vacuum states and observables;
- the chosen compactness / projective / direct-limit mechanism;
- infinite-volume Euclidean physical state;
- preservation of reflection positivity, gauge invariance, clustering, and nontrivial observable content.

**Status: downstream.**

---

## 13. Continuum OS / Wightman construction

Required later:

- continuum Euclidean invariance;
- reflection positivity;
- regularity sufficient for OS reconstruction;
- clustering / decay compatible with the spectral interpretation;
- nontrivial physical Hilbert space and observable algebra;
- same-root OS / Wightman reconstruction.

**Status: downstream.**

---

## 14. Continuum mass gap target

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

A fixed-volume eigenvalue, an auxiliary transfer operator, or a limit not linked through the same formal root is insufficient.

**Status: downstream / not yet proved.**

---

## 15. Recent canonical theorem units

| PR | Status | Role | Merge commit |
| --- | --- | --- | --- |
| #4739 | merged | local-mean carrier in fluctuation sector | `8720285a644d3c4aea9634ce7a3a7af0a5816dbb` |
| #4740 | merged | measurable fixed-right kernel-section Fubini | `cb6615d51807a3a09e229f50870dc1ad4a87139b` |
| #4741 | merged | genuine joint density factorization | `b2d8b7d2cb79ea8c7c3ac5bac1295a96094f4bdb` |
| #4742 | merged | fixed-left orientation | `73683c70fd7788ac39de0bdfe927ed9c9aefd0a8` |
| #4743 | merged | weighted kernel-section Fubini | merged |
| #4744 | merged | physical law presentation | merged |
| #4745 | merged | explicit kernel-section Markov kernel | `9536aa310f849c6e4dbdc4fe9cd6db14f842e23c` |
| #4746 | merged | exact joint-law disintegration | `f53b58bee9ef3678eecd90be33e1d6adbc951ffc` |
| #4747 | merged | genuine one-link fiber = kernel-section law | `c9253c3546c35d717209403919ddbd26a189c6fa` |
| #4748 | merged | diagonal section L2 carrier | `cfcb224b26aaf3dad280e2f655729bb7652554f2` |
| #4749 | merged | diagonal section conditional energy = norm² | `ddb0ede53028d49c4f27e7a2c20c4c242fdf556b` |
| #4750 | merged | canonical split Markov kernel + fiber mean | `4c67a6166d02f0f555968bbab2470c2f77981915` |
| #4751 | merged | canonical split-kernel Fubini identity | `bf4fd8a43eaa64d398928a00dc1c71d3642459d7` |
| #4752 | merged | canonical fiber-mean variance minimality | `b5a049b005ce65446ed67b06ac79232b36a3416a` |
| #4753 | merged | canonical fiber variance <= centered residual | `f1283f7b5720e87133685e016721592257e1429c` |
| #4754 | merged | canonical fiber variance <= CondExpL2 residual² | `37f89cb4b07fee26f2ee241e094ae14c0c62d251` |
| #4755 | merged | canonical variance = canonical centered residual | `f874d7be6ac9d889f71738bf4b50e312aae9d336` |
| #4756 | merged | genuine joint kernel-section lintegral disintegration | `47b17b27722d6a4cd103a04143cafbdae782df9a` |
| #4757 | merged | canonical variance in kernel-section residual coordinates | `cd62b7087cee27e4bf55efa7330043e92a2c2860` |
| #4758 | merged | canonical fiber mean = kernel-section one-link integral | `7e842185bda3d8230dd4437217f1f33109a76bc2` |
| #4759 | merged | diagonal reference fiber = kernel-section law | `436a1b0ec53182ee7262605368a408b53dc5f240` |
| #4760 | merged | diagonal remote projection = kernel-section integral | `0c977c5f346cd661072b5dc52a36b2a7037b6894` |
| #4761 | merged | canonical mean = diagonal remote projection; residual = fluctuation | `6bd73357bd0aa4d358923806e648a04300253e4c` |
| #4762 | closed / unmerged | duplicate/superseded draft; not authority | — |

---

## 16. Lean 4 / mathlib engineering rules

1. **Fresh head first.** Re-observe theorem-carrier, recent PRs, and the current PR head before branch creation, write, CI classification, and merge judgment.
2. **Exact head only.** Never classify a stale workflow SHA.
3. **Step-level CI.** Inspect `Changed Lean fast check`, not only run-level state.
4. **Completion receipt.** Require the exact-head commit-status receipt before merge.
5. **Read the whole module.** On RED, inspect the full changed Lean file, CompileSmoke, imports, dependent signatures, and pinned APIs.
6. **Pinned mathlib authority.** Current master may guide syntax but cannot override the pinned revision.
7. **Dependent rewrite discipline.** Avoid broad reverse `rw` across dependent measures / Lp carriers.  Build a typed proof term, then prefer `simpa only [h] using hBase`.
8. **Typeclass promotion is not automatic from theorem names.** If a theorem proves `IsProbabilityMeasure` or `IsMarkovKernel`, install it locally with `letI` before asking downstream APIs for `SFinite` / `IsSFiniteKernel`.
9. **Instance presentation matters.** `Measure.pi` can retain hidden finite-type / measurable-space instance terms.  Reuse the exact local instance bundle when definitional alignment matters.
10. **autoImplicit = false.** Unknown identifiers generally indicate a missing defining import or unavailable declaration, not an implicit-variable fallback.
11. **Source/target orientation.** Verify exact theorem signatures before applying physical response bounds.
12. **No arbitrary L2 pointwise evaluation.** Move through bounded concrete representatives and a.e. identities.
13. **No accidental volume factor.** Do not reintroduce cardinality factors through naive finite Cauchy/telescoping.
14. **No new comparison factor in localPart.** The current route is designed to close with coefficient one.

---

## 17. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe `formal/real-hilbert-uniform-coercive-strong-limit`;
2. expected theorem-bearing baseline is `6bd73357bd0aa4d358923806e648a04300253e4c` unless a later theorem merge has occurred;
3. if this docs refresh is merged, keep its docs-only pointer distinct from the theorem-bearing baseline;
4. retain #4749 as the diagonal section conditional-energy = section-L2-norm² authority;
5. retain #4754 as the coefficient-one canonical fiber variance <= global CondExpL2 residual² authority;
6. retain #4756 as the genuine joint / vacuum-kernel-section Fubini authority;
7. retain #4757 as the kernel-section residual-coordinate presentation;
8. retain #4758--#4761 as the exact identification of the canonical genuine residual with the diagonal remote kernel-section fluctuation;
9. prove the integrated equality between the #4761 residual energy and the vacuum average of #4749 section norm²;
10. package the resulting source-specific localPart carrier and prove `||localPart_s|| <= ell_s`;
11. separately prove `||R_{s,t}|| <= K_{t,s} ||x_t||`;
12. instantiate #4723;
13. apply #4713 -> #4687 / #4691;
14. close bounded-core positive-beta Poincare;
15. extend through #4650 -> #4651 to the volume-independent finite-volume physical gap.

The immediate theorem unit is:

**Integrate the #4761 canonical-residual/diagonal-fluctuation identity through the exact kernel-section disintegration and identify it with the #4749 vacuum-averaged section L2 energy.**
