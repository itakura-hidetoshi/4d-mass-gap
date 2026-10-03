# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Current theorem status — through merged PR #5061

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
  -> arbitrary nonzero physical two-mode vector
       = nonzero degree-one trace polynomial              #5061
  -> feature-analysis kernel trivial on the two-mode span #5061
  -> completed H1-D5 impossible at positive SU(2) coupling #5061
~~~

At positive coupling, #5058 proves that every nonzero finite primary normalized-trace polynomial has strictly positive bare temporal-crossing quadratic form in the exact H1-D5 half-weight endpoint measure. #5059 identifies the chosen continuous SU(2) Wilson two-mode span with the literal trace pair 1,r, where r = 1 - E_W. #5061 closes the remaining finite-dimensional bridge: every nonzero physical two-mode vector is represented by a nonzero degree-one trace polynomial, its physical one-slab quadratic form is exactly the half-weight crossing form, and the physical feature-analysis map therefore has trivial kernel on the two-mode span.

Feeding that theorem into the already formalized #5045/#5044/#5043 obstruction chain gives a theorem-level no-go statement:

~~~text
one finite scale with beta > 0
  ->
not completed H1-D5 compatibility.
~~~

The old route

~~~text
H1-D5 compatibility
  -> vacuum alignment
  -> explicit centered q0
~~~

is therefore closed as a failed model-facing identification at positive SU(2) coupling. It must not be resurrected under a renamed equivalent statement. The active finite-volume problem is now to construct a strictly weaker excitation-level seam that transports the already-proved q0 estimate without forcing rank-one collapse of the physical one-slab transfer.

A complete continuum four-dimensional Yang--Mills existence and Wightman mass-gap theorem is not yet claimed.

## Authority checkpoint — 2026-10-03 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Fresh theorem-carrier HEAD | a72ba16e1e6a1596db974ee0c20b6ffc8d79c73b |
| Latest theorem merge | PR #5061 — positive-coupling SU(2) completed H1-D5 no-go |
| #5061 exact PR head | d8e08f83dc422a3d4636a01559afdffa5d176a21 |
| #5061 validation | PR Lean Fast Check run 37117871784: completed / success; exact-head receipt success |
| #5059 trace-span theorem | merge 4a318081c47a724c6ca92c9953f9a5067f91bf1b |
| #5058 strict crossing theorem | merge d9b9de525c213739e9cdb145890c1f14e97b4f3b |
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
- continuous SU(2) two-mode carrier equals the literal normalized-trace span;
- every nonzero physical SU(2) two-mode vector has a nonzero degree-one trace-polynomial representative;
- the physical one-slab feature-analysis operator is injective on the SU(2) two-mode span at beta > 0;
- the old completed H1-D5 compatibility is impossible whenever at least one finite scale has beta > 0.

### Not yet closed

- replacement of the refuted H1-D5 seam by the weaker excitation-level model-facing compatibility actually needed for explicit centered q0 decay;
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

## 8. H1-D5 no-go closure and replacement frontier — #5061

#5061 closes the exact bridge that remained after #5058/#5059.

For an arbitrary physical SU(2) two-mode vector

~~~text
x != 0,
x in span{f0,f1},
~~~

the theorem first produces coefficients c0,c1, not both zero, such that the ambient Haar-L2 class of x is represented by the literal degree-one normalized-trace polynomial

~~~text
P(r) = c0 + c1 r.
~~~

The physical one-slab quadratic form is then identified exactly with the #5058 half-weight temporal-crossing quadratic form. Therefore

~~~text
x != 0
  ->
Q_cross(P) > 0
  ->
A_phys x != 0.
~~~

Hence the physical one-slab feature-analysis operator has trivial kernel on the explicit two-mode span. The existing #5045/#5044/#5043 reduction then yields

~~~text
beta(n) > 0
  ->
not H1-D5 completed compatibility at scale n.
~~~

A repository-level wrapper also proves that existence of any finite scale with positive coupling suffices.

### Current finite model-facing target

Do not attempt another proof of the old completed H1-D5 statement. The next theorem must be strictly weaker and excitation-level.

The preferred geometry to inspect first is:

~~~text
actual centered finite-OS excitation
  -> PhysicalPairCarrier
  -> TopTop^perp
  -> existing full-pair non-top q0 receiver
  -> q0^m decay.
~~~

This combines the strongest parts of the earlier R1 and R3 candidates and avoids identifying the finite OS vacuum with the physical one-slab Perron state. If direct carrier/top-orthogonality cannot be generated from the existing gauge-fixed and centering theorems, the fallback is a centered-sector-only comparison or a direct projective-dynamics comparison.

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
PR #5061 exact head:
  d8e08f83dc422a3d4636a01559afdffa5d176a21

PR Lean Fast Check:
  run 37117871784
  completed / success

exact-head completion receipt:
  success

theorem-bearing merge:
  a72ba16e1e6a1596db974ee0c20b6ffc8d79c73b
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
| #5061 | arbitrary physical two-mode vector -> nonzero trace polynomial -> feature-kernel injectivity -> positive-coupling completed H1-D5 no-go |

## Primary current modules

- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedH1D5SU2NoGo.lean
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
