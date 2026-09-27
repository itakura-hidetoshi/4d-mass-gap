# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-27 JST

Repository:

**itakura-hidetoshi/4d-mass-gap**

Unique authoritative theorem-carrier branch:

**formal/real-hilbert-uniform-coercive-strong-limit**

Fresh theorem-bearing baseline immediately before this documentation refresh:

**693c2ef8673cdfe40ec6615fc7d9c3e600dc9745**

This is the merge commit of PR **#4861**, **Charge full-direct update error to sweep path loss**.

Validated exact head of #4861:

**8f4b83ea6388b1f654fb4b67a3407c3fa6b13d68**

Validation:

- PR Lean Fast Check run **36313199617 — success**
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

The current formal line has closed the former positive-beta response/RMS/stationarity obstruction and now reaches an exact physical finite-update error estimate.

The strongest current endpoint is not yet a Poincare theorem. PR #4861 proves, for a canonical bounded sweep-stage representative family,

~~~text
fullOffDiagonalSum(source)
  =
directOffDiagonalSum(source)
  + sum_target ResponseL2(source,target)
~~~

and therefore

~~~text
integral_C
  sum_source
    ||fullOffDiagonalSum(source)
      - directOffDiagonalSum(source)||^2

  <=
rhoResp(s,beta)
  * ofReal(6 * sweepPathLoss(f)).
~~~

On the canonical strictly positive response interval,

~~~text
rhoResp(s,beta) < 1,
~~~

so

~~~text
errorEnergy
  <=
ofReal(6 * sweepPathLoss(f)).
~~~

The unresolved finite-volume positive-beta task is now the **direct finite-update / ordered-sweep closure** needed to turn this update-error estimate into a bounded-core six-spatial Poincare inequality.

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

## 11. Current theorem-bearing endpoint — PR #4861

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

This is the current authoritative endpoint.

It is stronger semantically than an auxiliary response-energy theorem because its left-hand side is now a physical finite-update error.

---

## 12. Current frontier — direct finite-update closure

Do **not** return to the old RMS / variance / pointwise-majorant route.

The remaining finite-volume obstruction is:

### 12.1 Direct off-diagonal finite-update term

The object still needing identification/control is:

~~~text
directOffDiagonalSum(source).
~~~

For each target, the direct term is the target conditional mean of a concrete section change under one fixed target law.

It is **not automatically definitionally equal** to a canonical sweep-stage residual vector.

Therefore the next theorem must prove the correct bridge rather than assume it.

Two acceptable routes are:

- an exact ordered/telescoping identity at the Hilbert-vector level, if the formal stage structure supports it;
- an exact or coefficient-one energy comparison through the already-proved direct-energy law-reordering chain (#4728--#4735), if vector identification is not canonical.

The proof must avoid:

- finite-cardinality Cauchy loss;
- an arbitrary source/target sum factor;
- unjustified pointwise evaluation of L2 quotient representatives;
- silently identifying different source-specific carriers.

### 12.2 Recommended immediate theorem unit

The preferred next unit is:

1. specialize the directDifferenceL2 semantics to the canonical stage representative F_target;
2. rewrite its squared norm through the existing canonical direct-energy / ordered-law identities;
3. use the preserved canonical prefix witness to connect that ordered direct energy to the actual stage-residual / path-loss structure;
4. sum over targets/sources only after the coefficient-one or orthogonal/telescoping identity is established.

The desired schematic output is something like:

~~~text
directUpdateEnergy
  <=
C_direct * ofReal(6 * sweepPathLoss(f)),
~~~

with C_direct volume-independent and ideally C_direct = 1 if the exact geometry supports it.

Do **not** freeze C_direct before Lean proves the correct normalization.

### 12.3 Combine direct and response pieces

Once directUpdateEnergy is controlled, combine with #4861.

The target is an actual physical current-value/update bound whose left side controls the centered bounded-core vector or the exact frame quantity required by the six-spatial Poincare receiver.

The algebra should preserve the exact decomposition as long as possible and avoid a factor-two triangle inequality unless formally unavoidable.

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

---

## 20. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe **formal/real-hilbert-uniform-coercive-strong-limit**;
2. expected theorem-bearing baseline is **693c2ef8673cdfe40ec6615fc7d9c3e600dc9745** unless a later theorem merge has occurred;
3. retain #4791--#4799 as closed stationarity / target-residual return;
4. retain #4800--#4818 as closed RMS feedback and vacuum response-energy chain;
5. retain #4831--#4849 as the closed fixed-background energy / bidirectional Schur / actual response-sum route;
6. retain #4850--#4852 as exact physical full/direct/response decomposition;
7. retain #4853--#4858 as canonical prefix / vector telescoping / exact stage path-loss closure;
8. retain #4859--#4861 as strict positive response cutoff and physical full-minus-direct error control;
9. do not rebuild the old pointwise RMS majorant route;
10. next inspect the canonical directDifferenceL2 of the stage representatives against #4728--#4735 direct-energy law reordering;
11. prove a volume-free direct finite-update -> sweep path-loss bridge;
12. combine with #4861 to close the bounded-core six-spatial Poincare inequality;
13. only then apply the existing full-L2 / random-scan / transfer-gap receivers;
14. continue to thermodynamic and continuum construction after the volume-uniform finite-volume gap is formally closed.

The immediate mathematical frontier is:

**Identify or control the canonical direct finite-update sum by the exact ordered sweep path-loss structure, without a finite-volume cardinality loss, and combine that result with PR #4861 to obtain the positive-beta bounded-core six-spatial Poincare inequality.**
