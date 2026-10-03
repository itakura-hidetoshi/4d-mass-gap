# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Current theorem status — through merged PR #5059

The finite-volume positive-coupling transfer-gap route is closed with explicit uniform constants

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

The q0 estimate is available on the full completed physical pair non-top sector.

The major change since the previous README is that H1-D4 is now closed, while H1-D5 has turned into an explicit no-go analysis rather than a compatibility theorem that should simply be assumed or forced.

The current exact picture is:

~~~text
H1-D4
  independent endpoint gauge-fixed pair sector
    =
  completed physical pair carrier                         CLOSED #5029

H1-D5 candidate completed compatibility
  -> literal Wilson path identity                        #5031-#5038
  -> strict-positive subtop obstruction                  #5039-#5040
  -> rank-one one-slab transfer consequence              #5041
  -> literal Wilson quadratic obstruction                #5042
  -> two-mode Wilson Gram determinant = 0                #5043
  -> feature-image dependence                            #5044
  -> two-mode feature-kernel nontriviality residual      #5045
  -> half-weight crossing Gram                           #5046-#5048
  -> protected selected Fock sector                      #5049-#5051
  -> positive-density trace/four-edge strictness         #5052-#5058
  -> continuous SU(2) two-mode span = span{1,r}          #5059
~~~

At positive coupling, #5058 proves that every nonzero finite primary normalized-trace polynomial has strictly positive bare temporal-crossing quadratic form in the exact H1-D5 half-weight endpoint measure. #5059 proves that the chosen continuous SU(2) Wilson two-mode representatives span exactly the literal trace pair 1,r, with r = 1 - E_W.

The remaining H1-D5 step is therefore small and finite-dimensional: transport an arbitrary nonzero vector in the chosen SU(2) two-mode span to a nonzero trace-polynomial coefficient vector, apply #5058, and push the resulting strict crossing positivity back through #5046/#5045/#5044/#5043. The expected endpoint is a theorem-generated contradiction to the old completed H1-D5 compatibility at beta > 0.

That means the old route

~~~text
H1-D5 compatibility
  -> vacuum alignment
  -> explicit centered q0
~~~

must not be treated as the final model-facing route unless the compatibility statement is weakened. The repository is now exposing why the naive completed identification is too strong.

A complete continuum four-dimensional Yang--Mills existence and Wightman mass-gap theorem is not yet claimed.

## Authority checkpoint — 2026-10-03 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Fresh theorem-carrier HEAD | 4a318081c47a724c6ca92c9953f9a5067f91bf1b |
| Latest theorem merge | PR #5059 — continuous SU(2) two-mode span = normalized-trace span |
| #5059 exact PR head | 445a95c59706c277a878dc67fa35d2e69c297ed7 |
| #5059 validation | PR Lean Fast Check run 37115303435: completed / success; exact-head receipt success |
| #5058 strict crossing theorem | merge d9b9de525c213739e9cdb145890c1f14e97b4f3b |
| #5058 validation | exact head 10c7cfe0ebbaa51f9aa9f3a2d437230fcb1c33a7; run 37115300163 success; receipt success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md)

The default branch main is not theorem authority. It is a documentation mirror.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

README / ROADMAP-only commits are docs-only and do not replace the latest theorem-bearing snapshot.

## Current claim boundary

### Closed

- beta = 0 physical transfer gap equals 1;
- positive-beta finite-volume coercivity;
- volume/rank/scale-uniform gap floor 1/3072;
- q0 = 3071/3072 and uniform q0^m decay;
- full completed physical pair non-top q0^m decay;
- one-dimensional finite physical top eigenspace;
- one-dimensional completed pair top-top block;
- scale-coherent projective L2 carrier with nonzero centered strong limits under the projective cylinder/readout data;
- explicit SU(N) Wilson two-mode boundary representatives;
- canonical-sign finite OS vacuum identified with the concrete Wilson boundary vacuum;
- independent endpoint gauge fixedness of the canonical-sign vacuum pair;
- H1-D4: independent endpoint gauge-fixed pair sector equals the completed physical pair carrier;
- H1-D5 reduction from completed compatibility to a literal finite Wilson two-mode Gram degeneracy;
- exact positive-density / selected-Fock decomposition of the H1-D5 crossing Gram;
- one-slice positive-density trace Gram nondegeneracy and positive-degree feature moments;
- positive-coupling strict four-edge and bare crossing Gram for every nonzero finite primary trace polynomial;
- continuous SU(2) two-mode carrier equals the literal normalized-trace span.

### Not yet closed

- final theorem that the old completed H1-D5 compatibility is impossible at beta > 0 on the actual SU(2) two-mode carrier;
- replacement of that too-strong seam by the weaker model-facing compatibility actually needed for explicit centered q0 decay;
- transport of finite q0 dynamics to the nonzero projective continuum excitation;
- spacing-scaled physical-time dynamics;
- final OS Hamiltonian spectral lower bound;
- Wightman / energy-momentum mass-gap theorem.

## 1. Finite-volume gap route

The leakage, Schur, renewal, complete-order, twelve-spatial and physical-centering layers are closed.

The endpoint is

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

1/2304 <= kappa_12(s,beta),

1/3072 <= physical transfer gap,

q0 = 3071/3072.
~~~

No lattice-volume, link-count or gauge-rank loss appears in this finite-step contraction constant.

## 2. Scale-coherent projective carrier

#4993--#4998 construct the projective finite-OS scale-coherence lane.

The important distinction remains:

- the independent-product carrier is useful for simultaneous finite-scale comparison but centered fresh-coordinate strong limits vanish;
- the projective carrier is the scale-coherent lane supporting nonzero centered strong limits.

The projective construction is kinematically available. What is still missing is model-facing coherence of the evolved finite states and a physical-time scaling law.

## 3. Explicit two-mode and full-pair q0 lane

#4999--#5009 construct explicit SU(N) Wilson two modes and place the q0 estimate on the full completed physical pair non-top sector.

#5010--#5016 then prove:

~~~text
finite physical top eigenspace is one-dimensional,

completed pair top-top block is one-dimensional,

uncentered primary-plaquette pair is physical,

old vacuum-alignment problem reduces to:
  physical-pair membership
  + one proposed transfer compatibility seam.
~~~

#5017/#5018 identify the canonical-sign OS vacuum concretely and prove arbitrary independent endpoint gauge fixedness.

## 4. H1-D4 is closed — #5022--#5029

This layer should no longer be listed as an open problem.

The chain is:

- #5022: physical pair carrier is contained in the independently gauge-fixed pair sector;
- #5023: identify the algebraic pair Gauss projection range;
- #5024: prove dense range of the real L2 external tensor;
- #5025: identify the real L2 tensor completion with product L2;
- #5026: identify the completed pair Gauss projection range;
- #5027: construct the left Riesz representative for product-L2 kernels;
- #5028: descend independent gauge-fixed pairings through the Gauss projection;
- #5029: prove exact equality

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Thus canonical-sign vacuum-pair physicality follows from the already-proved endpoint gauge fixedness.

## 5. H1-D5 reduction and no-go chain — #5030--#5045

#5030 reduces the old H1-D6 vacuum-normalized route to H1-D5 alone.

Then H1-D5 is progressively exposed:

### #5031--#5035: literalize the compatibility

~~~text
completed compatibility
  -> physical matrix coefficient identity
  -> literal finite Wilson integral
  -> finite Wilson boundary-vacuum moment
  -> unfixed positive-half path-kernel moment
  -> partition normalization cancels.
~~~

### #5036--#5038: operator consequence

The path message M_H is identified with positive-half transfer powers, giving

~~~text
T^(H+3) = ||T||^2 T^(H+1).
~~~

### #5039--#5041: spectral rigidity

A strict-positive subtop eigenmode contradicts H1-D5.

Compact positivity then theorem-generates such a mode whenever the top-orthogonal restriction is nonzero. Hence H1-D5 forces that restriction to vanish.

Together with top-eigenspace simplicity:

~~~text
H1-D5
  -> normalized physical one-slab transfer is rank one.
~~~

### #5042--#5045: finite two-mode residual

The rank-one consequence is rewritten as a literal finite Wilson quadratic statement.

H1-D5 forces the explicit two-mode Wilson Gram determinant to vanish.

Equivalently, the two feature-analysis images must be linearly dependent, or the one-slab feature-analysis operator must have nontrivial kernel on the explicit two-dimensional physical span.

This is the exact finite-dimensional obstruction target.

## 6. Positive-density crossing strictness — #5046--#5058

### #5046--#5048: exact endpoint measure

The two-mode Wilson determinant is rewritten as a half-weighted temporal-crossing Gram.

The half-weight is exposed as an equivalent strictly positive density over one-slice Haar.

Thus the H1-D5 residual is placed on the exact endpoint measure used by the physical one-slab kernel.

### #5049--#5051: protected selected Fock sector

The literal temporal crossing kernel is decomposed into:

~~~text
Schur-PSD remainder
  +
residual degree-zero scalar
  * genuine primary four-edge selected Fock kernel.
~~~

No residual link is dropped.

### #5052--#5057: one-slice strictness

The repository proves:

- infinite range of the primary SU(2) normalized trace on one spatial slice;
- nondegenerate finite trace-power Gram matrices under arbitrary equivalent finite positive density;
- theorem-generated strictly positive degree moments for every nonzero finite trace polynomial;
- lift from scalar trace moment to cyclic Hilbert feature moment;
- reflection to genuine four-edge feature moment;
- strictly positive genuine four-edge Gram;
- specialization to the exact H1-D5 half-weight endpoint measure.

### #5058: strict bare crossing Gram

At beta > 0, every nonzero finite primary normalized-trace polynomial P satisfies

~~~text
0 <
  integral integral
    P(A) P(B)
    K_cross(A,B)
    dmu_half(A) dmu_half(B).
~~~

This is the cancellation-free strictness theorem needed to contradict the old H1-D5 rank-one/degeneracy consequence.

## 7. Continuous SU(2) two-mode trace span — #5059

The normalized-Haar two-mode Gram--Schmidt family already spans the literal seed pair 1,E_W.

#5059 lifts that equality back to continuous representatives using injectivity of ContinuousMap.toLp under normalized Haar and proves, for SU(2),

~~~text
span{chosen continuous two modes}
  =
span{1, E_W}
  =
span{1, r},
~~~

where

~~~text
r = normalized real trace = 1 - E_W.
~~~

Each chosen continuous two-mode representative therefore has literal normalized-trace coefficients.

No explicit Gram--Schmidt coefficients are required.

## 8. Immediate frontier after #5059

### F1. Close the SU(2) two-mode strictness wrapper

For an arbitrary nonzero

~~~text
x in span{f0,f1},
~~~

use #5059 to produce a nonzero trace polynomial P representing x.

Then apply #5058:

~~~text
Q_cross(P) > 0.
~~~

Transport this equality to the exact two-mode physical crossing form.

Completion target:

~~~text
x != 0
  ->
half-weight crossing quadratic form(x) > 0.
~~~

Equivalently, the one-slab physical feature-analysis operator is injective on the explicit two-mode span.

### F2. Push strictness back through the existing H1-D5 reduction

Use #5045/#5044/#5043 to obtain

~~~text
feature map injective on two-mode span
  -> two feature images linearly independent
  -> two-mode Wilson Gram determinant != 0
  -> not H1-D5 completed compatibility.
~~~

For beta > 0 this should become a theorem-generated no-go statement, not a heuristic.

### F3. Replace the too-strong H1-D5 seam

Once the no-go theorem is registered, do not attempt to prove the same completed compatibility by another route.

The next model-facing bridge must be weaker and sufficient for q0 transport without forcing the physical one-slab transfer to rank one.

Natural targets include:

- direct carrier/top-orthogonality of the actual centered finite-OS excitation;
- a comparison only on the centered excitation sector rather than on the vacuum;
- a direct q0 estimate for the actual finite-OS excitation;
- a projective finite-dynamics comparison that does not identify the periodic OS vacuum with the one-slab Perron state.

The exact replacement theorem should be chosen only after the H1-D5 no-go is formally closed.

## 9. Continuum continuation

After the correct finite model-facing seam is identified:

~~~text
finite q0 control
  -> evolved projective coherence
  -> nonzero projective continuum excitation
  -> spacing-scaled semigroup / generator estimate
  -> OS Hamiltonian
  -> spectral gap
  -> Wightman mass gap.
~~~

The fixed discrete q0 must not be interpreted directly as a fixed physical-time mass rate when lattice spacing tends to zero.

## 10. Lean / CI workflow

Latest theorem validation:

~~~text
PR #5059 exact head:
  445a95c59706c277a878dc67fa35d2e69c297ed7

PR Lean Fast Check:
  run 37115303435
  completed / success

exact-head completion receipt:
  success

theorem-bearing merge:
  4a318081c47a724c6ca92c9953f9a5067f91bf1b
~~~

Previous key strictness validation:

~~~text
PR #5058 exact head:
  10c7cfe0ebbaa51f9aa9f3a2d437230fcb1c33a7

PR Lean Fast Check:
  run 37115300163
  completed / success

exact-head completion receipt:
  success
~~~

Recent Lean engineering lessons:

- inspect the complete changed module, not only the first reported line;
- preserve the pinned mathlib API rather than coding against current master;
- avoid duplicate local typeclass instances on dependent product/subtype carriers;
- prefer literal List/Finset carriers already used by the defining kernel when Fintype definitional equality is fragile;
- use explicit local equalities across let aliases before simp;
- prefer calc + Finset.sum_congr + named rewrites to broad simp_rw when transporting ContinuousMap.toLp expressions;
- use congrArg for dependent integral or inner-product rewrites when rw does not see through local aliases;
- use ContinuousLinearMap / LinearMap extensionality pointwise rather than forcing global definitional equality;
- once an unchanged exact head is GREEN, do not rerun strict Lean validation merely for reassurance;
- docs-only README / ROADMAP updates are not theorem-bearing changes.

## Recent theorem progression

| PR | Contribution |
| --- | --- |
| #5022--#5029 | close H1-D4: independent gauge-fixed pair sector = physical pair carrier |
| #5030 | reduce vacuum-normalized H1-D6 to H1-D5 |
| #5031--#5038 | reduce H1-D5 to a physical one-slab power identity |
| #5039--#5041 | prove H1-D5 forces rank-one physical one-slab transfer |
| #5042--#5045 | reduce contradiction to two-mode Wilson Gram / feature-kernel nondegeneracy |
| #5046--#5048 | rewrite residual as positive-density half-weight crossing Gram |
| #5049--#5051 | protect and factor an exact four-edge selected Fock sector |
| #5052--#5054 | positive-density one-slice trace Gram and positive-degree moments |
| #5055--#5057 | lift scalar moments to cyclic/four-edge strictness at the H1-D5 endpoint measure |
| #5058 | strict bare temporal-crossing Gram for every nonzero trace polynomial at beta > 0 |
| #5059 | continuous SU(2) two-mode span = normalized-trace span |

## Primary current modules

- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeFeatureKernelResidual.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModePositiveDensityCrossingGram.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeCrossingSelectedSectorPSD.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeCrossingSelectedFactorization.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityGram.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityMoment.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityFeatureMoment.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityFourEdgeMoment.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightFourEdgeGram.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5HalfWeightCrossingGramStrict.lean
- MGAP4D/MathlibAnalytic/SpecialUnitaryWilsonEnergySU2ContinuousTwoModeTraceSpan.lean

For the exact continuation sequence, see [ROADMAP.md](ROADMAP.md).
