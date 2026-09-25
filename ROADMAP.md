# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-25 JST

Repository:

**`itakura-hidetoshi/4d-mass-gap`**

Unique authoritative theorem-carrier branch:

**`formal/real-hilbert-uniform-coercive-strong-limit`**

Fresh theorem-bearing baseline immediately before this documentation refresh:

**`e4c878398f0d0aa183cfc86eb8970c7c3593114e`**

This is the merge commit of PR **#4773**, **Integrate background-dependent Schur coercivity over outer law**.

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
- exact beta-zero physical endpoint;
- high-temperature physical response / influence / covariance machinery;
- genuine one-link and six-spatial conditional expectations;
- volume-independent positive-beta row/column Schur control;
- link-indexed sweep-stage local-energy profile;
- exact genuine-joint / kernel-section disintegration;
- canonical one-link fiber variance and coefficient-one global CondExpL2 comparison;
- exact identification of the canonical residual with the diagonal kernel-section fluctuation;
- exact vacuum-averaged diagonal section L2 energy identity;
- genuine-joint canonical localPart L2 vector;
- coefficient-one bound `||localPart_s|| <= ell_s`;
- source-specific response L2 lift;
- configuration-independent canonical pin-free RMS envelope;
- background-dependent row and transpose Schur coercivity integrated over arbitrary outer measures and the physical vacuum law.

The old localPart obstruction is closed.

The current finite-volume positive-beta obstruction is the **actual observable-specific recurrence / decomposition** needed to instantiate either the dependent source-carrier assembler or the new outer-background Schur receiver.

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
- the complete local import closure;
- dependent theorem signatures;
- the pinned mathlib API;
- typeclass and elaboration structure;
- whether the failure is static preflight/import routing or actual Lean compilation.

Merge judgment requires:

- the PR's current exact `head_sha`;
- terminal success of **Changed Lean fast check**;
- the success exact-head completion receipt.

---

## 2. Stable downstream receiver spine

These layers are available and should not be rebuilt.

### 2.1 Genuine ground-state L2 / transfer receiver

PRs #4650--#4652 supply:

- bounded-concrete -> full genuine joint L2 closure;
- six-spatial residual / Rayleigh receivers;
- physical transfer-gap receiver;
- finite Hilbert projection infrastructure.

### 2.2 Exact beta-zero endpoint

PRs #4653--#4682 close:

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

PRs #4683--#4687 and the later strict-sweep refinements provide the actual physical envelope `K_A` and a volume-independent scalar

~~~text
0 <= q_phys(s,beta) < 1
~~~

which controls both maximum rows and maximum columns uniformly in finite volume and in the outer background `A`.

Both ordinary and transpose one-sided receivers are available.

The transpose orientation is

~~~text
u_s <= ell_s + sum_t K_A(t,s) u_t.
~~~

### 2.4 Sweep local energy

PRs #4688--#4690 provide the canonical link-indexed sweep-stage local profile `ell_s` and

~~~text
(1/6) * sum_s ell_s^2
  <= E_6sp.
~~~

### 2.5 Dependent response assembler

PR #4723 accepts source-specific normed carriers `E_s`.

Its intended abstract inputs are

~~~text
x_s = localPart_s + sum_t R_{s,t}

||localPart_s|| <= ell_s

||R_{s,t}|| <= K_{t,s} ||x_t||.
~~~

This receiver remains valid, but after #4773 there is also a scalar outer-background route which can bypass some same-carrier bookkeeping.

---

## 3. Closed localPart chain

### 3.1 Section-space and exact law infrastructure — #4738--#4761

The earlier chain established:

- local-mean kernel-section L2 carrier;
- fluctuation-sector placement;
- exact genuine joint = vacuum `tensor_m` kernel-section disintegration;
- genuine split one-link law = kernel-section one-link law;
- diagonal section L2 carrier;
- exact section conditional-square energy = section L2 norm squared;
- canonical split Markov kernel and measurable canonical fiber mean;
- canonical fiber variance minimality;
- canonical variance <= genuine one-link CondExpL2 residual norm squared;
- canonical mean = kernel-section one-link integral;
- diagonal remote projection = the same integral;
- canonical centered residual = diagonal remote kernel-section fluctuation.

PR #4761 was the last theorem in the previous documentation snapshot.

### 3.2 Lift across the whole target fiber — #4764

PR #4764 proves:

- off-target invariance of the direct normalized one-link law;
- the corresponding kernel-section one-link invariance;
- diagonal remote projection invariance under replacement of the stored target value;
- the #4761 residual identity for **every target-fiber value** over almost every retained outer context.

This removes the identity-inserted-representative restriction.

Merge:

**`768cb059cfed2847cd912abd614f23468dc6137d`**

### 3.3 Exact split fluctuation energy — #4765

The canonical variance is rewritten exactly as the lower integral of the diagonal remote fluctuation squared in target/off-target split coordinates.

No measure change or estimate is introduced.

Merge:

**`010fc4e6e6a964c65649b8838588269c39c6ae2c`**

### 3.4 Descend to physical vacuum / kernel-section laws — #4766

The split residual identity is transported through the target/off-target measure-preserving equivalence and then descended:

1. Haar -> literal kernel-section law by absolute continuity;
2. outer Haar -> physical vacuum law by absolute continuity.

Result:

~~~text
for vacuum-a.e. C,
  for kernel-section-a.e. A,
    canonical residual(C,A)
      = diagonal remote kernel-section fluctuation(C,A).
~~~

Merge:

**`7fcfcd38f27904c868d11dfd8bfe829e56eeacba`**

### 3.5 Exact integrated section energy — #4767

Insert the #4766 a.e. identity into the #4757 vacuum/kernel-section residual representation and use the exact section norm identity.

The resulting theorem is schematically

~~~text
CanonicalFiberVarianceFunctional
  =
integral_C
  ENNReal.ofReal (||r_C^KS||^2)
  d mu_vacuum(C).
~~~

Combining with the existing global residual bound gives

~~~text
integral_C ||r_C^KS||^2 d mu_vacuum
  <= ||f - P_target f||^2
~~~

with coefficient one.

Merge:

**`7bd02830473645ac76d2a6dd43bb5a5c11fc847f`**

### 3.6 Genuine-joint canonical localPart vector — #4768

PR #4768 packages the canonical fiber-mean centered residual as an actual vector

~~~text
localPart_target
  in genuine ground-state joint L2.
~~~

Its squared L2 norm is exactly the canonical fiber variance, and therefore inherits the coefficient-one CondExpL2 residual bound.

Merge:

**`42a01e847a4da1099509eaf21fda243cd09f6c89`**

### 3.7 Real norm bridge — #4769

The ENNReal squared inequality is converted into the real norm form

~~~text
||localPart_target||
  <=
||stageVector - P_target stageVector||.
~~~

The theorem is then specialized to bounded-concrete fixed-color sweep-stage representatives and canonical prefixes.

Merge:

**`f6334b1aa5b0e540dbd9ff02c780e0b0c2a58657`**

### 3.8 Stage-profile closure — #4770

PR #4770 proves the finite-list fact that the residual norm at the occurrence of a projection label in an ordered sweep is bounded by the total stage amplitude attributed to that label.

Using the canonical `Finset.univ.toList` sweep, every spatial link gets a bounded representative satisfying

~~~text
||localPart_s|| <= ell_s.
~~~

This is the exact coefficient-one localPart theorem required by the response spine.

Merge:

**`b12ec21f58c06e036cc2b81cc655706cdb71ffa0`**

**Status: localPart closed.**

---

## 4. Response and outer-Schur infrastructure after localPart closure

### 4.1 Source-specific response L2 lift — #4771

PR #4724 had already defined

~~~text
E_s = L2(nu_s),
~~~

where `nu_s` is the source-specific pair/background probability law.

PR #4771 adds a generic response vector constructor and proves:

if

~~~text
|R(z)| <= M
~~~

almost everywhere, then

~~~text
||R||_{E_s} <= M.
~~~

In particular, an a.e. bound

~~~text
|R_{s,t}(z)|
  <= K(t,s) * amplitude_t
~~~

lifts to

~~~text
||R_{s,t}||
  <= K(t,s) * amplitude_t
~~~

with no loss.

Merge:

**`0d6351704115da08e093417297e50506bcf61028`**

**Status: generic response L2 lift closed; concrete observable instantiation remains.**

### 4.2 Canonical configuration-independent pin-free RMS kernel — #4772

The stagewise RMS spine originally uses a background-dependent physical envelope

~~~text
K_A(target,source).
~~~

PR #4772 proves the pointwise domination

~~~text
K_A(target,source)
  <=
K_pinfree(target,source),
~~~

where `K_pinfree` is generated from the canonical fixed-right response profile and is independent of `A`.

The existing full-envelope centered RMS estimate therefore upgrades to the same canonical pin-free coefficient while preserving target/source orientation.

Merge:

**`d92764b7cf374187fddad50080bad44af05ff0df`**

**Status: closed.**

### 4.3 Outer-lintegral Schur receiver — #4773

PR #4773 supplies a complementary route which keeps the actual background-dependent physical envelope.

For any outer measure `mu`, if pointwise in `A`

~~~text
profile_A(target)
  <=
local_A(target)
  + sum_source K_A(target,source) profile_A(source),
~~~

then

~~~text
integral_A ofReal(
  (1 - q_phys)^2 * sum_e profile_A(e)^2
)
<=
integral_A ofReal(
  sum_e local_A(e)^2
).
~~~

The theorem also proves the transpose orientation

~~~text
profile_A(source)
  <=
local_A(source)
  + sum_target K_A(target,source) profile_A(target),
~~~

and physical-vacuum specializations of both orientations.

The scalar `q_phys(s,beta)` is unchanged because the row/column bounds were already uniform in `A`.

Validated exact head:

**`5325474e940e57b54b4e00d85a30c519f58cdca4`**

CI:

**PR Lean Fast Check #15126 / run 36145120296 — success**

Exact-head completion receipt:

**success**

Merge:

**`e4c878398f0d0aa183cfc86eb8970c7c3593114e`**

**Status: outer row + transpose Schur integration closed.**

---

## 5. Current theorem frontier

The next work should **not** rebuild localPart, Schur row/column estimates, or outer integration.

The remaining finite-volume positive-beta issue is the concrete observable-specific recurrence.

There are now two legitimate interfaces.

### 5.1 Route A — instantiate the dependent source-carrier assembler

Construct, for each source `s`, actual vectors in one chosen carrier `E_s`:

~~~text
x_s
localPart_s
R_{s,t}
~~~

with exact decomposition

~~~text
x_s
  = localPart_s + sum_t R_{s,t}.
~~~

Then prove:

~~~text
||localPart_s|| <= ell_s
~~~

using #4770, and

~~~text
||R_{s,t}||
  <= K(t,s) ||x_t||
~~~

using the physical response theory and #4771 / #4772 as appropriate.

#### Important same-carrier issue

The current canonical localPart vector from #4768--#4770 lives naturally in the genuine joint L2 space, whereas #4771 packages responses naturally in the source-pair/background L2 space.

Do **not** silently identify these carriers.

A Route-A completion must either:

- realize state/localPart/response in a common source-specific carrier; or
- give a genuine isometric / norm-preserving transport theorem before invoking #4723.

### 5.2 Route B — pointwise outer-background recurrence then #4773

This route avoids forcing all terms into a common dependent Hilbert carrier before the Schur step.

Construct scalar fields

~~~text
profile A e
localProfile A e
~~~

such that for every outer background `A`

~~~text
profile A source
  <=
localProfile A source
  + sum_target K_A(target,source) * profile A target.
~~~

Then apply the transpose theorem from #4773.

The remaining work is to choose those fields from the actual sweep-stage / centered-RMS construction and identify the physical-vacuum lower-integral of the local term with the already-closed local energy from #4767--#4770.

This route has the advantage that the actual physical envelope `K_A` remains inside the pointwise recurrence and never needs to be pulled through the outer integral.

### 5.3 Orientation rule

Always preserve

~~~text
K(target,source).
~~~

The recurrence needed by the transpose receiver is

~~~text
u_source
  <= ell_source
     + sum_target K(target,source) u_target.
~~~

Do not replace it by `K(source,target)`.

### 5.4 Immediate recommended theorem unit

The clean next unit is an **observable-specific pointwise transpose recurrence** at a canonical bounded-concrete sweep stage.

It should:

1. choose the stage representative once;
2. define the target amplitudes from the actual centered RMS / conditional residual quantities;
3. use #4770 for the direct/local contribution;
4. use #4772 for a configuration-independent coefficient if the source-pair L2 route is chosen, or retain `K_A` if the #4773 route is chosen;
5. prove the exact transpose one-sided recurrence with no finite-cardinality loss.

After that, the Schur algebra itself is already closed.

---

## 6. Positive-beta bounded-core Poincare target

Once the observable-specific recurrence is available, obtain schematically

~~~text
(1/6) *
(1 - q_phys(s,beta))^2 *
global_profile_energy
  <=
E_6sp.
~~~

The remaining normalization theorem must identify / dominate the global profile energy by the centered bounded-core norm required for the Poincare receiver.

Do not freeze a final numerical coefficient until that exact normalization is formalized.

**Status: open.**

---

## 7. Full genuine joint L2 and finite-volume physical gap

After bounded-core Poincare:

1. apply #4650 to extend to full genuine joint L2;
2. use #4651 to obtain six-spatial Rayleigh `q(beta) < 1`;
3. apply the physical transfer-gap receiver;
4. obtain a finite-volume gap lower bound independent of volume on the certified positive-beta interval;
5. transport to the exact Hamiltonian normalization and vacuum-orthogonal sector.

**Status: downstream.**

---

## 8. Thermodynamic / infinite-volume construction

Required later:

- compatible finite-volume embeddings / restrictions;
- consistency of vacuum states and observables;
- the chosen compactness / projective / direct-limit mechanism;
- infinite-volume Euclidean physical state;
- preservation of reflection positivity, gauge invariance, clustering, and nontrivial observable content.

**Status: downstream.**

---

## 9. Continuum OS / Wightman construction

Required later:

- continuum Euclidean invariance;
- reflection positivity;
- regularity sufficient for OS reconstruction;
- clustering / decay compatible with the spectral interpretation;
- nontrivial physical Hilbert space and observable algebra;
- same-root OS / Wightman reconstruction.

**Status: downstream.**

---

## 10. Continuum mass-gap target

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

A fixed-volume eigenvalue, an auxiliary transfer operator, or a limit not linked through the same formal root is insufficient.

**Status: downstream / not yet proved.**

---

## 11. Recent theorem units

| PR | Status | Role | Merge commit |
| --- | --- | --- | --- |
| #4764 | merged | lift residual identity across the whole target fiber | `768cb059cfed2847cd912abd614f23468dc6137d` |
| #4765 | merged | canonical variance = split diagonal fluctuation energy | `010fc4e6e6a964c65649b8838588269c39c6ae2c` |
| #4766 | merged | descend residual identity to vacuum / kernel-section laws | `7fcfcd38f27904c868d11dfd8bfe829e56eeacba` |
| #4767 | merged | canonical variance = vacuum diagonal section L2 energy | `7bd02830473645ac76d2a6dd43bb5a5c11fc847f` |
| #4768 | merged | package canonical residual in genuine joint L2 | `42a01e847a4da1099509eaf21fda243cd09f6c89` |
| #4769 | merged | canonical residual L2 norm <= one-link stage residual | `f6334b1aa5b0e540dbd9ff02c780e0b0c2a58657` |
| #4770 | merged | canonical localPart norm <= sweep-stage local profile | `b12ec21f58c06e036cc2b81cc655706cdb71ffa0` |
| #4771 | merged | source-specific pair/background L2 response lift | `0d6351704115da08e093417297e50506bcf61028` |
| #4772 | merged | canonical pin-free full-envelope RMS kernel | `d92764b7cf374187fddad50080bad44af05ff0df` |
| #4773 | merged | arbitrary-outer-law row + transpose Schur integration | `e4c878398f0d0aa183cfc86eb8970c7c3593114e` |

PR #4762 is closed / unmerged and is not theorem authority.

---

## 12. Lean 4 / mathlib engineering rules

1. **Fresh head first.** Re-observe theorem-carrier, recent PRs, and the current PR head before branch creation, write, CI classification, and merge judgment.
2. **Exact head only.** Never classify a stale workflow SHA.
3. **Step-level CI.** Inspect `Changed Lean fast check`, not only run-level state.
4. **Completion receipt.** Require the exact-head commit-status receipt before merge.
5. **Read the whole module.** On RED, inspect the full changed Lean file, CompileSmoke, imports, dependent signatures, and pinned APIs.
6. **Distinguish static preflight from Lean compilation.** A missing local defining import can fail before Lean starts.
7. **Import the defining module.** Do not assume a nearby historical import path defines the declaration; #4773 exposed this with `VacuumMeasure`.
8. **Pinned mathlib authority.** Current master may guide syntax but cannot override the pinned revision.
9. **Dependent rewrite discipline.** Avoid broad reverse `rw` across dependent measures / Lp carriers. Prefer typed intermediate terms and narrow `simpa only [...] using ...`.
10. **Typeclass promotion is not automatic.** If a theorem proves `IsProbabilityMeasure` or `IsMarkovKernel`, install it locally with `letI` before downstream `SFinite` / `IsSFiniteKernel` APIs.
11. **Instance presentation matters.** Hidden `Measure.pi` / finite-type / measurable-space instance terms can matter definitionally.
12. **`simp` versus `simpa`.** `simp at h` rewrites a hypothesis; `simpa using h` closes the current goal. There is no `simpa ... at h` form.
13. **Measurable equivalence direction matters.** Use `symm_apply_apply` for `e.symm (e x) = x`, and `apply_symm_apply` for `e (e.symm y) = y`.
14. **Source/target orientation.** Verify exact theorem signatures before applying response bounds.
15. **No arbitrary L2 pointwise evaluation.** Move through bounded concrete representatives and a.e. identities.
16. **No accidental volume factor.** Do not reintroduce finite-cardinality Cauchy/telescoping losses.
17. **No new localPart factor.** The localPart route is closed with coefficient one.

---

## 13. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe `formal/real-hilbert-uniform-coercive-strong-limit`;
2. expected theorem-bearing baseline is `e4c878398f0d0aa183cfc86eb8970c7c3593114e` unless a later theorem merge has occurred;
3. if this docs refresh is merged, keep its docs-only pointer distinct from the theorem-bearing baseline;
4. retain #4767 as exact vacuum-averaged diagonal section energy authority;
5. retain #4768--#4770 as the closed genuine-joint localPart / sweep-stage profile chain;
6. retain #4771 as the source-specific response L2 lift;
7. retain #4772 as the canonical configuration-independent pin-free RMS envelope;
8. retain #4773 as the arbitrary-outer-law row + transpose Schur integration authority;
9. do **not** reopen the localPart proof;
10. construct the actual observable-specific transpose recurrence / decomposition;
11. choose explicitly between the dependent-carrier route (#4723) and the outer-background scalar route (#4773), or prove a bridge showing them equivalent for the chosen physical profiles;
12. close the bounded-core positive-beta six-spatial Poincare inequality;
13. apply #4650 -> #4651 for the full-L2 finite-volume physical gap;
14. continue to thermodynamic / infinite-volume and continuum OS-Wightman construction.

The immediate mathematical frontier is:

**Build the actual observable-specific transpose recurrence using the already-closed coefficient-one localPart theorem and the physical RMS response estimates, then feed it into the #4773 outer-integral transpose Schur receiver (or equivalently instantiate #4723 after placing all terms in one legitimate source-specific carrier).**
