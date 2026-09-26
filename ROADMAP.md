# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-26 JST

Repository:

**itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline immediately before this documentation refresh:

**d1a2e7bb9189643cf7c973568fab5dd39065bbf6**

This is the merge commit of PR **#4787**, **Compare ordered old and updated target variances**.

Validated exact head of #4787:

**05d6555377d6774c823e5d5d4318a5a858c95bd6**

CI:

**PR Lean Fast Check run 36213674095 — success**

Exact-head completion receipt:

**chatgpt-ci-receipt/PR Lean Fast Check — success**

The default branch **main is not theorem authority**.

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
- canonical one-link fiber variance and coefficient-one CondExpL2 comparison;
- genuine-joint canonical localPart L2 vector;
- coefficient-one bound ||localPart_s|| <= ell_s;
- source-specific pair/background response L2 carrier;
- exact observable-specific target-law response;
- exact two-law RMS amplitude in the same source-pair L2 carrier;
- center-independence of the response and pointwise-center freedom for RMS;
- canonical choice of the actual second target-law fiber mean;
- exact reordering of the first cross energy to ordered coordinates;
- exact Pythagorean decomposition with no factor-two loss;
- exact identification of response-square energy with the response L2 norm-square;
- generic Harnack evariance transport under measure domination;
- pointwise ordered old-target variance <= Harnack factor * updated-target variance.

The former localPart obstruction is closed.

The former fixed-center RMS obstruction is closed.

The former hidden law-ordering mismatch is explicit and reduced to a single updated target-fiber variance.

The current finite-volume positive-beta obstruction is the **outer integration / stationarity return of the updated variance, followed by reconnection to the genuine target residual/profile and closure of the actual target-indexed RMS majorant / transpose recurrence**.

---

## 1. Pinned formal environment

Lean:

**v4.30.0-rc2**

mathlib:

**5450b53e5ddc75d46418fabb605edbf36bd0beb6**

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

- the PR's current exact head_sha;
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

The positive-beta influence chain provides:

~~~text
K_A(target,source) >= 0
max-row(K_A) <= q_phys(s,beta)
max-column(K_A) <= q_phys(s,beta)
0 <= q_phys(s,beta) < 1
~~~

uniformly in finite volume and in the outer background A on the certified high-temperature interval.

Both ordinary and transpose one-sided receivers are available.

The transpose orientation is:

~~~text
u_source
  <= ell_source
     + sum_target K_A(target,source) * u_target.
~~~

PR #4773 already integrates this Schur coercivity over arbitrary outer measures and the physical vacuum law.

### 2.4 Sweep local energy

The canonical six-spatial sweep profile ell_s satisfies:

~~~text
(1/6) * sum_s ell_s^2 <= E_6sp.
~~~

### 2.5 Dependent source-carrier assembler

PR #4723 accepts source-specific normed carriers E_s and the abstract decomposition

~~~text
x_s = localPart_s + sum_t R_{s,t}

||localPart_s|| <= ell_s

||R_{s,t}|| <= K(t,s) ||x_t||.
~~~

It remains valid, but the present theorem line has increasingly favored the source-pair / outer-law scalar route because it avoids unjustified identification of distinct L2 carriers.

---

## 3. Closed coefficient-one localPart chain

The localPart chain from #4738 through #4770 is closed and should not be reopened.

Its key output is:

~~~text
||localPart_s|| <= ell_s
~~~

for every genuine spatial link, with coefficient one.

The proof passes through:

- kernel-section local-mean L2;
- exact genuine-joint disintegration;
- canonical fiber mean and variance;
- canonical residual = diagonal remote fluctuation;
- a.e. descent to vacuum / kernel-section laws;
- exact vacuum-averaged diagonal section energy;
- genuine-joint residual L2 packaging;
- real norm extraction;
- canonical sweep-prefix / stage-profile bridge.

The exact integrated canonical variance authority remains PR #4767.

The genuine-joint localPart vector / stage profile authorities remain #4768--#4770.

---

## 4. Response / RMS / ordered-cross chain

### 4.1 Concrete target-law response — #4775

PR #4775 realizes the actual observable-specific target-law response on the exact source-pair/background carrier.

Off the diagonal it is the difference between two target-fiber conditional means, one based at the first source sample and one based at the second source sample.

Merge:

**828605b8527f2a35c729bafccd75691560fcb595**

### 4.2 Response L2 — #4776

PR #4776 proves measurability and MemLp 2 and packages the response as

~~~text
Response_{source,target} in L2(nu_source).
~~~

It preserves the target/source response orientation.

Merge:

**4b3409720569252ca7a258a59c138636837d1b68**

### 4.3 Exact RMS amplitude L2 — #4777

PR #4777 defines the exact two-law centered energies and

~~~text
RMS(z) = sqrt(E_first(z) + E_second(z)),
~~~

packages RMS in the same source-pair carrier, and proves

~~~text
||Response_{source,target}||
  <= K_pin(target,source) * ||RMS_{source,target}||.
~~~

No cardinality loss is introduced.

Merge:

**fee8782246351c60b50262212fb0a83ba007bfef**

### 4.4 Center freedom — #4778

The response is independent of the common scalar center.

Therefore the response may stay at a fixed reference center while the RMS side uses an arbitrary pointwise center.

Merge:

**5d8425f94a9cb0f9ee3ab3b01ad91fa7a2988ef1**

### 4.5 Canonical second-law center — #4779

Choose the actual second target-law fiber mean as the pointwise center.

Then:

~~~text
SecondMean(secondFiberMean) = 0
~~~

exactly.

The remaining RMS contribution is therefore the first-law cross energy.

Merge:

**09cb36cf91d175e673f5f98c59005e651a2342c7**

---

## 5. Exact first-cross reduction

### 5.1 Reorder the law — #4780

Construct the canonical ordered section and transport the complete first-law cross energy exactly to

~~~text
mu_source(dC)
  kappa_source(C)(dv)
  kappa_target(C)(dg).
~~~

Merge:

**8b53b9e07efe22d117a62815e4e91c619d362ddc**

### 5.2 Expose literal coordinates — #4781

The ordered residual becomes literal:

~~~text
X_v(g) = F(left, C[source <- v][target <- g]).
~~~

Sampling and centering use different target laws:

~~~text
sample:  g ~ kappa_target(C)
center:  mean of X_v under kappa_target(C[source <- v]).
~~~

This is the exact remaining law mismatch.

Merge:

**253383daa562428ab4768a9a49dc425998b9097f**

### 5.3 Pythagorean split — #4782

Introduce the old-law mean m_old.

For each ordered outer point:

~~~text
E_old[(X_v - m_new)^2]
  =
E_old[(X_v - m_old)^2]
  + (m_old - m_new)^2.
~~~

The second term is exactly the squared target-law response.

No triangle inequality and no factor two are used.

Merge:

**e4953e7c0d3235051f85dd0263cfad2c34882fdd**

### 5.4 Lift to outer law — #4783

The Pythagorean split is lifted exactly to the complete ordered outer measure.

Merge:

**0d1d34c6920c9a3c4a9a79411ceb44422c359de5**

### 5.5 Response-square = response L2 norm-square — #4784

Using the exact source-pair law reordering and the a.e. representative of the source-pair response vector:

~~~text
ordered integral response^2
  =
ofReal(||ResponseL2||^2).
~~~

Merge:

**d5af7e9420fdfe7bf99d3e37e5e571fe0c9738f2**

### 5.6 Global exact split — #4785

The first cross energy is now:

~~~text
firstCrossEnergy
  =
integral oldTargetVariance
  + ofReal(||ResponseL2||^2).
~~~

The response-square term is no longer a new analytic unknown.

Merge:

**150b8611f8a7d63ba347b893e263d008e91622af**

---

## 6. Harnack comparison of the remaining variance

### 6.1 Generic measure / evariance comparison — #4786

PR #4786 exposes the normalized-law domination implicit in the physical background-update Harnack argument.

For a single off-fiber background update:

~~~text
mu_old <= K_H(beta) • mu_new
mu_new <= K_H(beta) • mu_old

K_H(beta) = ofReal((exp(32 beta))^2).
~~~

It also proves the generic theorem:

~~~text
mu <= K • nu
  =>
evariance_mu(X) <= K * evariance_nu(X).
~~~

The proof uses variance minimality and measure monotonicity, not a triangle inequality.

Merge:

**ab2dc7dcaa1b965e2b0aed94e0812c48ff1c06fc**

### 6.2 Ordered old variance -> updated variance — #4787

PR #4787 identifies the old and updated centered energies with Mathlib variance/evariance and specializes #4786.

Pointwise on ordered (C,v):

~~~text
ofReal(oldVariance(C,v))
  <=
ofReal((exp(32 beta))^2)
  * ofReal(updatedVariance(C,v)).
~~~

No factor two, response coefficient, or finite-cardinality factor is introduced.

Validated exact head:

**05d6555377d6774c823e5d5d4318a5a858c95bd6**

CI:

**PR Lean Fast Check run 36213674095 — success**

Merge:

**d1a2e7bb9189643cf7c973568fab5dd39065bbf6**

---

## 7. Current theorem frontier

Do **not** rebuild:

- localPart;
- source-pair response L2;
- exact RMS amplitude;
- center freedom;
- ordered law reordering;
- Pythagorean split;
- response-square L2 identification;
- Harnack variance comparison;
- row/column Schur algebra;
- outer Schur integration.

The remaining chain is now much narrower.

### 7.1 Immediate theorem unit — integrate #4787

Integrate the pointwise inequality

~~~text
oldVariance(C,v)
  <= K_H(beta) * updatedVariance(C,v)
~~~

over the ordered second-background law.

Since K_H(beta) is scalar and independent of (C,v), the intended result is

~~~text
integral oldVariance
  <=
K_H(beta) * integral updatedVariance.
~~~

This step should use ENNReal / lintegral APIs directly and must not introduce a finite-cardinality factor.

### 7.2 Stationarity / pushforward return

Use the existing exact second-updated-background stationarity or pushforward theorem for the ordered source update to rewrite

~~~text
integral updatedVariance(C,v)
~~~

as an integral over the genuine source/reference background law.

The updated section is already centered at its own target-fiber mean, so this is the correct quantity to reconnect to the existing canonical target residual.

### 7.3 Reconnect to canonical target residual/profile

Identify or bound the stationarity-returned updated variance by the already-closed canonical target-fiber variance / genuine target conditional residual energy.

The coefficient-one local target residual authority remains #4767--#4770.

The desired schematic bound is:

~~~text
integral oldTargetVariance
  <=
K_H(beta) * genuineTargetVarianceEnergy.
~~~

### 7.4 Combine with #4785

Substitute into:

~~~text
firstCrossEnergy
  =
integral oldTargetVariance
  + ofReal(||ResponseL2||^2).
~~~

giving schematically:

~~~text
firstCrossEnergy
  <=
K_H(beta) * genuineTargetVarianceEnergy
  + ofReal(||ResponseL2||^2).
~~~

Then use the #4777 response/RMS norm estimate to close the actual target-indexed amplitude inequality.

### 7.5 Close the transpose recurrence

The required matrix orientation remains:

~~~text
K(target,source).
~~~

The target is an actual observable-specific recurrence of the form:

~~~text
u_source
  <= local_source
     + sum_target K(target,source) * u_target.
~~~

Feed this into the #4773 transpose outer-Schur receiver.

---

## 8. Positive-beta bounded-core Poincare target

Once the observable-specific target RMS majorant / transpose recurrence is closed, combine:

- coefficient-one localPart energy;
- volume-independent q_phys(s,beta) < 1;
- #4773 transpose Schur integration;
- six-spatial sweep energy normalization.

The target remains schematically:

~~~text
(1/6)
  * (1 - q_phys(s,beta))^2
  * global_profile_energy
  <=
E_6sp.
~~~

The final normalization between global profile energy and the centered bounded-core norm must be formalized exactly before freezing a numerical Poincare constant.

**Status: open.**

---

## 9. Full genuine joint L2 and finite-volume physical gap

After bounded-core Poincare:

1. apply #4650 to extend to full genuine joint L2;
2. use #4651 to obtain six-spatial Rayleigh q(beta) < 1;
3. apply the physical transfer-gap receiver;
4. obtain a finite-volume gap lower bound independent of volume on the certified positive-beta interval;
5. transport to the exact Hamiltonian normalization and vacuum-orthogonal sector.

**Status: downstream.**

---

## 10. Thermodynamic / infinite-volume construction

Required later:

- compatible finite-volume embeddings / restrictions;
- consistency of vacuum states and observables;
- the chosen compactness / projective / direct-limit mechanism;
- infinite-volume Euclidean physical state;
- preservation of reflection positivity, gauge invariance, clustering, and nontrivial observable content.

**Status: downstream.**

---

## 11. Continuum OS / Wightman construction

Required later:

- continuum Euclidean invariance;
- reflection positivity;
- regularity sufficient for OS reconstruction;
- clustering / decay compatible with the spectral interpretation;
- nontrivial physical Hilbert space and observable algebra;
- same-root OS / Wightman reconstruction.

**Status: downstream.**

---

## 12. Continuum mass-gap target

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

A fixed-volume eigenvalue, an auxiliary transfer operator, or a limit not linked through the same formal root is insufficient.

**Status: downstream / not yet proved.**

---

## 13. Recent theorem units

| PR | Status | Role | Merge commit |
| --- | --- | --- | --- |
| #4775 | merged | concrete target-law response | 828605b8527f2a35c729bafccd75691560fcb595 |
| #4776 | merged | target-law response in source-pair L2 | 4b3409720569252ca7a258a59c138636837d1b68 |
| #4777 | merged | exact target-law RMS amplitude in source-pair L2 | fee8782246351c60b50262212fb0a83ba007bfef |
| #4778 | merged | response center freedom / pointwise-center RMS | 5d8425f94a9cb0f9ee3ab3b01ad91fa7a2988ef1 |
| #4779 | merged | actual second-law fiber mean as canonical center | 09cb36cf91d175e673f5f98c59005e651a2342c7 |
| #4780 | merged | exact ordered first-cross law | 8b53b9e07efe22d117a62815e4e91c619d362ddc |
| #4781 | merged | literal ordered cross residual | 253383daa562428ab4768a9a49dc425998b9097f |
| #4782 | merged | exact Pythagorean split | e4953e7c0d3235051f85dd0263cfad2c34882fdd |
| #4783 | merged | global ordered Pythagorean lift | 0d1d34c6920c9a3c4a9a79411ceb44422c359de5 |
| #4784 | merged | ordered response-square = response L2 norm-square | d5af7e9420fdfe7bf99d3e37e5e571fe0c9738f2 |
| #4785 | merged | global cross energy = old variance + response L2 | 150b8611f8a7d63ba347b893e263d008e91622af |
| #4786 | merged | background-update Harnack evariance transport | ab2dc7dcaa1b965e2b0aed94e0812c48ff1c06fc |
| #4787 | merged | old ordered variance <= Harnack * updated variance | d1a2e7bb9189643cf7c973568fab5dd39065bbf6 |

PR #4774 is the previous docs-only refresh and is not a theorem-bearing mathematical step.

---

## 14. Lean 4 / mathlib engineering rules

1. **Fresh head first.** Re-observe theorem-carrier, recent PRs, and the current PR head before branch creation, write, CI classification, and merge judgment.
2. **Exact head only.** Never classify a stale workflow SHA.
3. **Step-level CI.** Inspect Changed Lean fast check, not only run-level state.
4. **Completion receipt.** Require the exact-head commit-status receipt before merge.
5. **Read the whole module.** On RED, inspect the full changed Lean file, CompileSmoke, imports, dependent signatures, and pinned APIs.
6. **Distinguish static preflight from Lean compilation.**
7. **Pinned mathlib authority.** Current upstream may guide syntax but cannot override the pinned revision.
8. **Dependent rewrite discipline.** Avoid broad reverse rw across dependent measures / Lp carriers.
9. **Typeclass promotion is not automatic.** Install theorem-proved IsProbabilityMeasure / IsMarkovKernel facts locally with letI when required.
10. **Instance presentation matters.** Hidden finite-type / measurable-space / Measure.pi terms may matter definitionally.
11. **rw transparency.** Ordinary rw searches with reducible transparency. Normalize local aliases / wrappers explicitly before rewriting if necessary.
12. **unfold order.** Named unfolds are sequential. Open an outer alias before the inner definitions it reveals.
13. **change is definitional.** Simplify theorem-level identities such as sub_zero before change.
14. **simpa final matching.** simpa using performs its final match at reducible transparency.
15. **Tight simp sets.** Remove unused simp arguments when the goal has already normalized by another path.
16. **Scalar action normalization.** For ENNReal measure/integral APIs, smul and multiplication may need explicit smul_eq_mul.
17. **Typed lambdas.** Add explicit domain types when expected-type inference leaves metavariables.
18. **Source/target orientation.** Preserve K(target,source).
19. **No arbitrary L2 pointwise evaluation.** Use bounded representatives and a.e. identities.
20. **No accidental volume factor.** Do not reintroduce finite-cardinality Cauchy/telescoping losses.
21. **No new localPart factor.** The coefficient-one localPart chain is closed.

---

## 15. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe **formal/real-hilbert-uniform-coercive-strong-limit**;
2. expected theorem-bearing baseline is **d1a2e7bb9189643cf7c973568fab5dd39065bbf6** unless a later theorem merge has occurred;
3. if this docs refresh is merged, keep its docs-only pointer distinct from the theorem-bearing baseline;
4. retain #4767--#4770 as the closed coefficient-one target/localPart chain;
5. retain #4775--#4777 as the concrete response + exact RMS L2 chain;
6. retain #4778--#4779 as center freedom + canonical second-law center;
7. retain #4780--#4785 as the exact ordered first-cross / Pythagorean / response-L2 split;
8. retain #4786--#4787 as the sharp Harnack old-to-updated variance comparison;
9. do not rebuild the Schur matrix or outer Schur integration;
10. integrate #4787 over the ordered outer law;
11. use second-updated-background stationarity / pushforward to return the updated variance;
12. identify it with the genuine target residual/profile;
13. combine with #4785 and close the target-indexed RMS majorant / transpose recurrence;
14. apply #4773 to close the positive-beta bounded-core six-spatial Poincare inequality;
15. apply #4650 -> #4651 for the full-L2 finite-volume physical gap;
16. continue to thermodynamic / infinite-volume and continuum OS-Wightman construction.

The immediate mathematical frontier is:

**Integrate the #4787 old-to-updated target-variance comparison over the ordered source-update law, use exact second-updated-background stationarity to return the updated variance to the genuine target-residual carrier, and combine that with the #4785 exact first-cross split to close the observable-specific target RMS majorant / transpose recurrence.**
