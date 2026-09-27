# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-27 JST

Repository:

**itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline immediately before this documentation refresh:

**f8b2cea5a780ae88362b17b7e404c937168d85fa**

This is the merge commit of PR **#4869**, **Transport backward direct variance by Harnack**.

Validated exact head of #4869:

**518ac2f99b341106e7b1f00f7726292d53c96fd6**

Validation:

- PR Lean Fast Check run **36323111870 — success**
- exact-head completion receipt **chatgpt-ci-receipt/PR Lean Fast Check — success**

The default branch **main is not theorem authority**.

Authority order:

1. fresh exact GitHub theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. historical summaries or memory.

A docs-only merge may advance the branch pointer without changing the theorem-bearing baseline above.

---

## 0. Claim boundary

The repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

The response-side finite-volume obstruction is closed through PR #4861:

~~~text
fullOffDiagonalSum(source)
  =
directOffDiagonalSum(source)
  + sum_target ResponseL2(source,target),
~~~

with

~~~text
integral_C
  sum_source
    ||fullOffDiagonalSum(source)
      - directOffDiagonalSum(source)||^2

  <=
rhoResp(s,beta)
  * ofReal(6 * sweepPathLoss(f)).
~~~

On the strict response cutoff this is bounded by ofReal(6 * sweepPathLoss(f)).

The direct side has now advanced further through PRs #4864--#4869:

~~~text
||DirectDifferenceL2||^2
  =
source-pair directMeanDifference energy
  <=
orderedDirectAverageEnergy,
~~~

then losslessly to the reversible backward carrier,

~~~text
ofReal ||DirectDifferenceL2||^2
  <=
integral BackwardDirectFiberEnergy,
~~~

followed by the exact pointwise split

~~~text
BackwardDirectFiberEnergy
  =
ofReal(BackwardDirectVarianceEnergy)
  + ofReal(BackwardDirectMean^2).
~~~

For source != target and D = C[target <- g], PR #4869 proves

~~~text
ofReal BackwardDirectVarianceEnergy(C,D)
  <=
ofReal((exp(32 * beta))^2)
  * ofReal BackwardDirectVarianceEnergy(C,C).
~~~

Thus the centered-variance part has been transported back to the diagonal source law with only the existing volume-independent Harnack law factor.

The unresolved finite-volume positive-beta task is now narrower:

1. identify the diagonal backward variance with the genuine source one-link residual / canonical fiber variance and then the exact stage-residual/path-loss carrier;
2. close the backward mean using its exact localPart + source-law-response decomposition without an arbitrary factor-two loss;
3. assemble finite targets/sources only after an orthogonal, Schur, or exact telescoping structure is available;
4. combine the resulting direct bound with #4861 to obtain the bounded-core six-spatial Poincare inequality.

---

## 1. Pinned formal environment

Lean:

**v4.30.0-rc2**

mathlib:

**5450b53e5ddc75d46418fabb605edbf36bd0beb6**

Do not use current mathlib master as theorem authority.

For theorem-bearing PRs, merge judgment requires:

- current exact head SHA;
- terminal success of **Changed Lean fast check**;
- exact-head completion receipt.

When CI is red, inspect:

- the exact reported error;
- the full changed Lean module;
- CompileSmoke;
- imports and dependent theorem signatures;
- pinned mathlib APIs;
- instance presentation;
- parser / notation presentation;
- whether the failure is preflight/cache/routing or actual Lean elaboration.

For docs-only changes, do not rerun Strict Lean merely because README/ROADMAP changed.

---

## 2. Stable roots and receivers

These layers are already available and should not be rebuilt.

### 2.1 Finite Wilson / OS / physical-transfer root

The finite-volume framework includes:

- periodic SU(N) Wilson measure infrastructure;
- one-slab transfer kernel;
- Osterwalder--Schrader / Gauss-law physical carrier;
- compact positive physical transfer;
- canonical nonnegative vacuum;
- ground-state transformed boundary and joint laws;
- genuine one-link and spatial-color conditional expectations.

### 2.2 Exact beta-zero endpoint

The beta-zero endpoint is closed:

~~~text
vacuum = spatial Haar
ground-state joint law = pair Haar
kappa_0 = 1/6
q_0 = 5/6
exact physical transfer gap = 1.
~~~

The older 1/16 consistency bound is not the exact beta-zero gap.

### 2.3 Existing full-L2 / Rayleigh / transfer-gap receivers

The downstream Hilbert receivers already exist.

Once a bounded-core six-spatial Poincare/frame estimate is proved with a volume-independent positive constant, the intended route is:

~~~text
bounded-core Poincare
  -> full genuine joint L2 closure
  -> six-spatial random-scan Rayleigh contraction
  -> physical transfer-gap receiver.
~~~

Do not rebuild these receivers before the bounded-core estimate is closed.

---

## 3. Closed local residual / sweep energy spine

The canonical local residual chain is closed.

For every genuine spatial link, bounded concrete sweep-stage representatives exist and the canonical residual is controlled with coefficient one.

The established sweep profile satisfies:

~~~text
(1/6) * sum_e localProfile(e)^2
  <=
E_6sp(f).
~~~

PRs #4853--#4858 strengthen the earlier profile bookkeeping substantially:

- the canonical prefix/suffix position of each link is preserved;
- exact vector telescoping of ordered projection sweeps is formalized;
- each canonical local-profile value is exactly the norm of its unique stage residual;
- the complete exact stage-residual energy is identified with sweep path loss.

The exact identity is:

~~~text
(1/6) * sum_e ||stageResidual_e||^2
  =
sweepPathLoss(f),
~~~

equivalently,

~~~text
sum_e ||stageResidual_e||^2
  =
6 * sweepPathLoss(f).
~~~

And the established nested-block theorem gives:

~~~text
sweepPathLoss(f)
  <=
E_6sp(f).
~~~

Thus

~~~text
sum_e ||stageResidual_e||^2
  <=
6 * E_6sp(f).
~~~

This path-loss carrier is the current preferred local-energy normalization.

---

## 4. Closed response / RMS / variance chain

The older #4787 documentation frontier is obsolete.

### 4.1 Observable-specific response and RMS

The exact target-law response is realized in a source-specific L2 carrier.

The exact two-law RMS amplitude is realized in the same carrier.

The response is center-independent, and the actual second target-law fiber mean can be used as the canonical pointwise center.

### 4.2 First-cross exact split

The ordered first-cross energy satisfies an exact Pythagorean split:

~~~text
firstCrossEnergy
  =
oldTargetVariance
  + response^2.
~~~

After outer integration:

~~~text
firstCrossEnergy
  =
integral oldTargetVariance
  + ofReal(||ResponseL2||^2).
~~~

No factor two is introduced.

### 4.3 Harnack variance transport and stationarity return

The old target variance is compared to the updated target variance using normalized-law domination with

~~~text
K_H(beta) = (exp(32 beta))^2.
~~~

The pointwise comparison is integrated exactly.

The second-updated background is returned by stationarity/pushforward.

The updated variance is reconnected to the genuine target residual / canonical fiber variance.

Therefore the former tasks

~~~text
integrate #4787
return updated variance by stationarity
reconnect to genuine target residual
~~~

are all **closed**.

### 4.4 Second-mean RMS feedback closure

PRs #4800--#4818 close:

- second-law-mean RMS L2;
- exact RMS energy split;
- law transport;
- Harnack + response bound;
- feedback squaring;
- strict feedback absorption;
- source-independent target majorants;
- target-indexed global majorants;
- vacuum response-energy matrix;
- response amplitudes.

The earlier RMS feedback obstruction is closed.

---

## 5. Fixed-background energy route

The earlier current-value dependent route exposed an invalid inference risk:

> an outer-energy RMS bound does not imply pointwise-in-background domination.

The formalization does not make that unjustified step.

Instead, PRs #4831--#4849 use a fixed-background **energy route**.

Closed components include:

1. fixed-background RMS Fubini;
2. fixed-background RMS target majorant;
3. fixed-background response Fubini;
4. fixed-background response energy bound;
5. square-root response amplitudes;
6. reciprocal-weight row bounds;
7. uniform off-diagonal shell mass;
8. beta-zero-vanishing bootstrap envelope;
9. configuration-independent bidirectional Schur contraction for K_pin;
10. transpose Schur bound for fixed-background response amplitudes;
11. target amplitude energy = genuine target residual energy;
12. vacuum integration;
13. finite target sum exchange;
14. canonical fiber variance / CondExpL2 residual control;
15. actual full response-sum L2 energy bound.

The matrix orientation remains:

~~~text
K_pin(target,source).
~~~

Never silently reverse it.

---

## 6. Bidirectional pin-free Schur closure

For the canonical pin-free kernel, a volume-independent shell coefficient is available:

~~~text
q_shell(s,beta) < 1
~~~

on the certified shell cutoff.

Both row and column sums are bounded by the same coefficient.

The resulting L2 Schur action satisfies schematically:

~~~text
sum_source
  (sum_target K_pin(target,source) v_target)^2

  <=
q_shell(s,beta)^2
  * sum_target v_target^2.
~~~

This is the transpose-capable response-energy engine used downstream.

---

## 7. Response residual coefficient and strict positive interval

The fixed-background response-residual coefficient is:

~~~text
rhoResp(s,beta).
~~~

It is finite on the relevant cutoff and satisfies:

~~~text
rhoResp(s,0) = 0.
~~~

PR #4859 proves continuity at beta = 0 and constructs a canonical volume-independent cutoff:

~~~text
betaResp(s) > 0
~~~

for every fixed s > 8 such that

~~~text
0 <= beta <= betaResp(s)
  =>
rhoResp(s,beta) < 1.
~~~

The strict response cutoff lies inside the existing bidirectional shell cutoff.

This is a genuine positive-beta interval, not only an endpoint statement.

---

## 8. Exact target-law L2 decomposition

PRs #4850--#4852 realize the physical source-update decomposition in one source-specific Hilbert carrier.

For target != source:

~~~text
fullDifferenceL2
  =
directDifferenceL2
  + responseL2.
~~~

The L2 classes are identified with the actual source-updated centered means.

After finite target assembly and exact diagonal-response cancellation:

~~~text
fullOffDiagonalSum(source)
  =
directOffDiagonalSum(source)
  + sum_target ResponseL2(source,target).
~~~

This equality is exact.

No response symmetry and no finite-cardinality inequality are used.

---

## 9. Canonical prefix / vector telescoping / stage residual closure

PR #4853 retains the exact canonical link position:

~~~text
canonicalList
  =
pre ++ e :: suffix,
~~~

together with e not in pre and the exact bounded stage representative.

PR #4854 proves generic vector telescoping:

~~~text
residualVectorSum(P, cs, x)
  =
x - sweep(P, cs, x).
~~~

PR #4855 specializes this to the genuine Yang--Mills fixed-color sweep.

PR #4856 proves the canonical local profile is exactly the norm of the unique stage residual.

PR #4857 charges the actual full response sums to these exact stage residuals.

PR #4858 identifies the entire stage-residual energy exactly with sweep path loss.

These statements should be reused, not reconstructed.

---

## 10. Strict response path-loss theorem

PR #4860 combines the exact path-loss carrier with the strict response cutoff.

On

~~~text
0 <= beta <= betaResp(s),
~~~

the actual full response-sum energy satisfies:

~~~text
integral_C
  sum_source
    ||sum_target ResponseL2(source,target)||^2

  <=
ofReal(6 * sweepPathLoss(f)).
~~~

The stronger coefficient-bearing version

~~~text
<= rhoResp(s,beta)
   * ofReal(6 * sweepPathLoss(f))
~~~

is also retained.

---

## 11. Response-side physical endpoint — PR #4861

PR #4861 moves the response estimate onto the **physical full-versus-direct update error**.

Using the exact finite target decomposition:

~~~text
fullOffDiagonalSum
  - directOffDiagonalSum
  =
sum_target ResponseL2.
~~~

Therefore:

~~~text
integral_C
  sum_source
    ||fullOffDiagonalSum(source)
      - directOffDiagonalSum(source)||^2

  <=
rhoResp(s,beta)
  * ofReal(6 * sweepPathLoss(f)).
~~~

On the strict cutoff:

~~~text
integral_C
  sum_source
    ||fullOffDiagonalSum(source)
      - directOffDiagonalSum(source)||^2

  <=
ofReal(6 * sweepPathLoss(f)).
~~~

This remains the closed response-side physical update theorem and is the result to combine with the direct-side closure below.

---

## 12. Direct finite-update advance — PRs #4864--#4869

### 12.1 Exact DirectDifferenceL2 energy and ordered-law comparison

PR #4864 identifies the direct-difference Hilbert energy exactly:

~~~text
||DirectDifferenceL2(target,source)||^2
  =
integral_(source-pair background)
  actualDirectMeanDifference^2.
~~~

PR #4865 then proves, with coefficient one,

~~~text
||DirectDifferenceL2(target,source)||^2
  <=
orderedDirectAverageEnergy(target,source).
~~~

The only inequality is the already established one-fiber probability-space estimate. No finite-cardinality factor is introduced.

### 12.2 Backward reversible carrier

PR #4867 transports the direct energy to the carrier already used by the #4736 local/law-response decomposition:

~~~text
ofReal ||DirectDifferenceL2(target,source)||^2
  <=
integral_(target heat-bath joint law)
  BackwardDirectFiberEnergy(source).
~~~

This step is lossless apart from the coefficient-one direct energy inequality already present in #4865.

### 12.3 Exact backward fiber Pythagoras

PR #4868 proves pointwise:

~~~text
BackwardDirectFiberEnergy
  =
ofReal(BackwardDirectVarianceEnergy)
  + ofReal(BackwardDirectMean^2).
~~~

The proof uses public mathlib variance identities. The local Pythagoras theorem in #4782 is private and is not treated as a cross-module API.

No triangle inequality and no factor two are introduced.

### 12.4 Harnack transport of the centered variance

PR #4869 uses the normalized background-update Harnack variance theorem from #4786.

For source != target and D = C[target <- g]:

~~~text
ofReal BackwardDirectVarianceEnergy(C,D)
  <=
ofReal((exp(32 * beta))^2)
  * ofReal BackwardDirectVarianceEnergy(C,C).
~~~

The orientation is fixed and must not be reversed:

~~~text
fiber = source
backgroundFiber = target.
~~~

This is the current theorem-bearing endpoint.

---

## 12A. Current frontier — diagonal variance, backward mean, finite assembly

Do **not** return to the old RMS / stationarity / pointwise-majorant route.

### 12A.1 Diagonal variance piece

The next preferred theorem unit is to identify

~~~text
BackwardDirectVarianceEnergy(C,C)
~~~

with the genuine diagonal source one-link residual / canonical fiber variance of the selected bounded sweep-stage representative.

The target shape is an exact identity or coefficient-one estimate, not a target-cardinality bound.

After this identification, reuse #4856--#4858 to connect the diagonal variance to the actual canonical stage-residual norm and sweepPathLoss.

### 12A.2 Backward mean piece

PR #4736 already proves exactly:

~~~text
BackwardDirectMean(C,D)
  =
DiagonalLocalMean(C)
  + BackwardLawResponse(C,D).
~~~

The local mean is already tied to the genuine kernel-section residual / canonical fiber-variance machinery.

The remaining task is to control the pure source-law response without immediately applying

~~~text
|a+b|^2 <= 2|a|^2 + 2|b|^2.
~~~

Prefer exact centering, orthogonality, covariance, or the existing response/Schur machinery if the formal carrier supports it.

### 12A.3 Finite target/source assembly

Do not sum individual target bounds until the correct structural identity is available.

Forbidden shortcuts remain:

- finite-cardinality Cauchy loss;
- a factor proportional to the number of spatial links;
- silent identification of source-specific L2 carriers;
- matrix-orientation reversal;
- arbitrary factor two when an exact Pythagorean/orthogonal split is available.

Only after the variance and mean pieces are closed should the finite target/source sums be assembled.

The desired schematic endpoint remains:

~~~text
directUpdateEnergy
  <=
C_direct(s,beta) * ofReal(6 * sweepPathLoss(f)),
~~~

with C_direct volume-independent. Do not freeze C_direct before Lean proves its normalization.

### 12A.4 Combine with #4861

Once directUpdateEnergy is closed, combine it with the exact full/direct/response identity and #4861.

The result should control the actual physical current-value/update quantity needed by the six-spatial Poincare receiver while preserving the exact decomposition as long as possible.

---

## 13. Positive-beta bounded-core six-spatial Poincare

This is the next major milestone.

Target shape:

~~~text
kappa(s,beta) * ||centered f||^2
  <=
E_6sp(f)
~~~

for bounded-core f, with:

~~~text
kappa(s,beta) > 0
~~~

uniformly in finite volume on a certified positive-beta interval.

The exact kappa must be derived only after the direct/full update normalization is closed.

Current status:

**OPEN**

---

## 14. Full genuine-joint L2 and finite-volume physical gap

After bounded-core Poincare:

1. extend from the bounded-concrete core to full genuine joint L2 using the existing closure machinery;
2. convert the frame/Poincare bound to six-spatial random-scan Rayleigh contraction;
3. invoke the existing physical transfer-gap receiver;
4. obtain a finite-volume gap lower bound uniform in volume on the certified positive-beta interval;
5. transport to the exact Hamiltonian normalization and vacuum-orthogonal sector.

Current status:

**DOWNSTREAM / OPEN**

---

## 15. Thermodynamic / infinite-volume construction

Required later:

- compatible finite-volume embeddings/restrictions;
- consistent vacuum states and observables;
- compactness/projective/direct-limit mechanism;
- infinite-volume Euclidean physical state;
- preservation of reflection positivity;
- gauge invariance;
- clustering;
- nontrivial observable content;
- transfer of the uniform positive finite-volume estimate.

Current status:

**DOWNSTREAM**

---

## 16. Continuum OS / Wightman construction

Required later:

- continuum Euclidean invariance;
- reflection positivity;
- sufficient regularity for OS reconstruction;
- clustering/decay compatible with a spectral gap;
- nontrivial physical Hilbert space and observable algebra;
- same-root OS/Wightman reconstruction.

Current status:

**DOWNSTREAM**

---

## 17. Continuum mass-gap target

The terminal theorem requires a continuum physical Hamiltonian with:

- a unique vacuum line;
- a strictly positive lower spectral edge on the vacuum-orthogonal sector.

A fixed-volume eigenvalue, an auxiliary transfer operator, or a limit disconnected from the same formal root is insufficient.

Current status:

**NOT YET PROVED**

---

## 18. Recent theorem units

### Stationarity / RMS closure

| PR | Status | Role |
| --- | --- | --- |
| #4791--#4799 | merged | integrate Harnack comparison, stationarity return, genuine target residual |
| #4800--#4810 | merged | second-mean RMS split, transport, feedback, strict absorption |
| #4812--#4818 | merged | uniform/target-indexed RMS majorants, vacuum response energy/amplitudes |

### Fixed-background energy route

| PR | Status | Role |
| --- | --- | --- |
| #4831--#4833 | merged | fixed-background RMS Fubini and target majorant |
| #4834--#4836 | merged | fixed-background response Fubini, energy, amplitudes |
| #4837--#4840 | merged | reciprocal shell bounds and bidirectional K_pin Schur |
| #4841--#4846 | merged | transpose response Schur, residual identity, vacuum target-sum exchange |
| #4847--#4849 | merged | sweep representatives, residual-energy charge, actual full response sums |

### Exact physical decomposition and path loss

| PR | Status | Role |
| --- | --- | --- |
| #4850 | merged | single-target L2 full = direct + response |
| #4851 | merged | semantic identification with actual source update |
| #4852 | merged | finite off-diagonal full/direct/response assembly |
| #4853 | merged | preserve canonical prefix/suffix witnesses |
| #4854 | merged | exact vector projection-sweep telescoping |
| #4855 | merged | fixed-color stage-vector exposure |
| #4856 | merged | local profile = exact stage residual norm |
| #4857 | merged | full response sums charged to exact stage residuals |
| #4858 | merged | exact stage residual energy = 6 * sweep path loss |
| #4859 | merged | strict positive response cutoff rhoResp < 1 |
| #4860 | merged | absorb response energy into sweep path loss |
| #4861 | merged | full-minus-direct update error charged to sweep path loss |
| #4864 | merged | exact DirectDifferenceL2 energy realization |
| #4865 | merged | coefficient-one direct L2 -> ordered direct average |
| #4867 | merged | direct L2 energy -> backward reversible carrier |
| #4868 | merged | exact backward direct fiber Pythagorean split |
| #4869 | merged | backward centered variance Harnack -> diagonal source law |

---

## 19. Lean 4 / mathlib engineering rules

1. Fresh theorem-carrier and exact PR head before any merge judgment.
2. Classify only the current exact head SHA.
3. Require Changed Lean fast check + exact-head receipt for theorem-bearing PRs.
4. Do not rerun Strict Lean merely for docs-only changes.
5. On RED, inspect the full changed module, CompileSmoke, imports, and pinned APIs.
6. Separate dependency/cache/routing failures from Lean elaboration failures.
7. Pinned mathlib is theorem authority.
8. Preserve K(target,source) orientation.
9. Do not pointwise evaluate arbitrary L2 quotient representatives.
10. Keep source-specific Hilbert carriers distinct unless an exact identification exists.
11. Avoid finite-cardinality Cauchy/telescoping losses.
12. Prefer exact Pythagorean / orthogonal / telescoping identities over factor-two triangle bounds.
13. Preserve already-proved coefficient-one local residual bounds.
14. For complicated finite sums in norms, package them as named Hilbert objects or use explicit Finset.sum.
15. Big-operator notation is convenient only while binder scope stays transparent.
16. After Lp.coeFn additive identities, expose pointwise application before rewriting if needed.
17. Use local letI for theorem-proved probability/Markov instances when APIs require typeclass search.
18. change requires definitional equality; theorem-level normalization must happen first.
19. Keep simp sets narrow and remove unused simp arguments.
20. Do not infer pointwise domination from an outer-energy inequality.
21. A private theorem in one Lean module is not an API in another module; use public mathlib lemmas or explicitly expose the theorem.

---

## 20. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe **formal/real-hilbert-uniform-coercive-strong-limit**;
2. expected theorem-bearing baseline is **f8b2cea5a780ae88362b17b7e404c937168d85fa** unless a later theorem merge has occurred;
3. retain #4791--#4799 as closed stationarity / target-residual return;
4. retain #4800--#4818 as closed RMS feedback and vacuum response-energy chain;
5. retain #4831--#4849 as the closed fixed-background energy / bidirectional Schur / actual response-sum route;
6. retain #4850--#4852 as exact physical full/direct/response decomposition;
7. retain #4853--#4858 as canonical prefix / vector telescoping / exact stage path-loss closure;
8. retain #4859--#4861 as strict positive response cutoff and physical full-minus-direct error control;
9. retain #4864--#4865 as exact direct L2 energy and coefficient-one ordered-law comparison;
10. retain #4867 as the lossless backward reversible-carrier transport;
11. retain #4868 as the exact backward direct variance + mean-square Pythagorean split;
12. retain #4869 as the Harnack transport of backward centered variance to the diagonal source law;
13. do not rebuild the old pointwise RMS majorant route;
14. next identify the diagonal backward variance with the genuine source residual / canonical fiber variance of the selected stage representative;
15. then close the backward mean using the exact local + law-response decomposition without an arbitrary factor-two loss;
16. assemble finite target/source sums only after a coefficient-one, Schur, orthogonal, or exact telescoping structure is established;
17. combine the direct closure with #4861 to prove the bounded-core six-spatial Poincare inequality;
18. only then apply the existing full-L2 / random-scan / transfer-gap receivers;
19. continue to thermodynamic and continuum construction after the volume-uniform finite-volume gap is formally closed.

The immediate mathematical frontier is:

**Identify the #4869 diagonal backward variance with the genuine one-link residual / canonical stage-residual carrier, close the backward mean through its exact localPart + source-law-response split without factor-two or cardinality loss, assemble the direct finite-update energy volume-freely, and combine it with PR #4861 to obtain the positive-beta bounded-core six-spatial Poincare inequality.**
