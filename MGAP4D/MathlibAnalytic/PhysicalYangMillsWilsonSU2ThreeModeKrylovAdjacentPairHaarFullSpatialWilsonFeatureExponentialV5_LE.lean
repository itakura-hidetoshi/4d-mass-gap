import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSpatialProductFeatureStoneWeierstrassV5_LD
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSingleLinkIntegralInjectiveV5_KV
import Mathlib.Tactic

/-!
# P4-Q2-LE — full genuine spatial Wilson kernel is a real-feature exponential

LD proves real-feature coordinate completeness on the ACTUAL finite
spatial configuration space, not merely on an individual SU(2) link.

Here we do not replace the Wilson action by an auxiliary Gram kernel.
We expand the literal original temporal-gauge crossing Wilson kernel,
which is a product of actual SU(2) Wilson relative kernels over every
physical spatial link, into ONE exponential of their real matrix-feature
pairings:

  K_cross(b,A,B) =
    exp (sum_(e in real spatial links)
       [-b + (b/2) <Phi(A_e),Phi(B_e)>]).

The full original one-slab Wilson transfer kernel is the SAME
exponential, sandwiched by the unchanged positive spatial Wilson
half-weights at the actual boundaries A and B.

This is exact at all real b (not merely positive coupling) and all
finite spatial H. It prepares the all-degree positive spatial
exponential Gram proof. It is not itself strict positive definiteness,
whole-space transfer injectivity, centered Wilson GI detection,
H1-C3 or a continuum Yang-Mills mass gap.
No sorry/admit, new axiom, rank hypothesis, or posterior replacement.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section SpatialProduct
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Phi" => specialUnitaryMatrixRealFeature 2

/-- The actual all-link SU(2) matrix-real-feature crossing exponent.
Every summand is from the defining representation at a real physical
spatial link, so the original Wilson normalization -b is retained. -/
noncomputable def p4Q2LE_originalSpatialCrossingFeatureExponent
    (b : ℝ) (A B : Cfg) : ℝ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
    -b + (b / 2) * inner ℝ (Phi (A e)) (Phi (B e))).sum

/-- A precise finite-list identity: the literal product of the
ACTUAL positive-beta SU(2) Wilson factors equals the exponential
of the sum of their ACTUAL real-feature exponents.
No spatial tensor independence hypothesis is introduced. -/
theorem p4Q2LE_originalWilsonRelativeKernel_listProduct_eq_featureExp
    (b : ℝ) (A B : Cfg) (es : List Link) :
    (es.map (fun e =>
      specialUnitaryWilsonRelativeKernel 2 b (A e) (B e))).prod =
      Real.exp ((es.map fun e =>
        -b + (b / 2) * inner ℝ (Phi (A e)) (Phi (B e))).sum) := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [p4Q2KV_originalWilsonRelativeKernel_eq_realFeatureExponential,
        p4Q2KR_originalSU2FeatureExponentialContinuous_apply, ih]
      rw [← Real.exp_add, ← Real.exp_add]
      try ring

/-- The ORIGINAL entire spatial-link Wilson crossing kernel is
one concrete finite real-feature exponential, without changing
even a single link, background or Haar measure. -/
theorem p4Q2LE_originalSpatialWilsonCrossing_eq_featureExponential
    (b : ℝ) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 b A B =
      Real.exp (p4Q2LE_originalSpatialCrossingFeatureExponent H b A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
    p4Q2LE_originalSpatialCrossingFeatureExponent
  exact p4Q2LE_originalWilsonRelativeKernel_listProduct_eq_featureExp
    H b A B (periodicHypercubicEvenSpatialSliceLinkList H)

/-- The COMPLETE original finite-volume temporal-gauge Wilson slab
kernel is the SAME exponential sandwiched by the ACTUAL positive
spatial Wilson half-weights. No normalization or vacuum is discarded. -/
theorem p4Q2LE_originalFullSpatialWilsonOneSlab_eq_featureExponential
    (b : ℝ) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b A B =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 b A *
        Real.exp (p4Q2LE_originalSpatialCrossingFeatureExponent H b A B) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 b B := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  rw [p4Q2LE_originalSpatialWilsonCrossing_eq_featureExponential]

/-- The genuine all-link exponential crossing factor is strictly
positive for every finite volume and boundary, directly from exp. -/
theorem p4Q2LE_originalSpatialWilsonCrossingFeatureExp_pos
    (b : ℝ) (A B : Cfg) :
    0 < Real.exp (p4Q2LE_originalSpatialCrossingFeatureExponent H b A B) :=
  Real.exp_pos _

/-- At nonnegative Wilson coupling, the feature exponential is
symmetric on actual physical spatial boundaries, because the
unchanged original crossing Wilson kernel is symmetric. -/
theorem p4Q2LE_originalSpatialFeatureExp_symmetric
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) :
    Real.exp (p4Q2LE_originalSpatialCrossingFeatureExponent H b A B) =
      Real.exp (p4Q2LE_originalSpatialCrossingFeatureExponent H b B A) := by
  rw [← p4Q2LE_originalSpatialWilsonCrossing_eq_featureExponential,
    ← p4Q2LE_originalSpatialWilsonCrossing_eq_featureExponential]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_symmetric
    H 2 (by norm_num) b hb A B

end SpatialProduct
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LE_originalWilsonRelativeKernel_listProduct_eq_featureExp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LE_originalSpatialWilsonCrossing_eq_featureExponential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LE_originalFullSpatialWilsonOneSlab_eq_featureExponential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LE_originalSpatialWilsonCrossingFeatureExp_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LE_originalSpatialFeatureExp_symmetric
