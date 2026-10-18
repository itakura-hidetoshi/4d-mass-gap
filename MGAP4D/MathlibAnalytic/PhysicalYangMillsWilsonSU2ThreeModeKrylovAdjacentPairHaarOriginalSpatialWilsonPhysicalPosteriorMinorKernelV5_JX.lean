import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonPhysicalTemporalCovarianceV5_JW
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorHaarMinorReconstructionV5_JN2
import Mathlib.Tactic

/-!
# P4-Q2-JX: exact two-point original Wilson posterior kernel for the physical spatial source

JN already proved that the REAL two-original-interacting-Wilson-posterior
two-point minor factors into a temporal SU(2) exponential increment
and a positive product of true Wilson posterior densities:

 M_b(g,h) = [exp(-b * (D(g)-D(h))) - 1] p0_b(h) ppi_b(g).

This module deduces the unconditional STRICT opposite temporal order
of this ORIGINAL minor at every frozen b>0. There is no weak-coupling
restriction and no differentiability assumption on the Perron vacuum.

JN2 proved that integrating M_b(g,h) in h is exactly p0_b(g)-ppi_b(g).
Here we integrate against an arbitrary continuous SU(2) receiver and
then insert the ORIGINAL Gauss-law anchored spatial Wilson source of JU.
The resulting genuine physical GI response is an EXACT iterated Haar
integral whose inner density minor has a known signed exponential factor.
Finally the original JK/JU spatial Wilson 2-context determinant is
identified with that specific literal exponential double integral,
including the nonzero original GI anchor and positive physical weight.

This does NOT prove the weighted full integral is nonzero: the genuinely
physical receiver may change sign and cancel between SU(2) link values.
It does NOT assume an independent-Haar posterior, synthetic source,
nondegenerate detector frame, new axiom/sorry, H1-C3, or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "M" => p4Q2JN_originalPosteriorTwoPointMinor H

/-- For any positive original frozen Wilson coupling, the TWO ACTUAL
interacting posterior density minor is strictly positive when
temporal Wilson action D strictly decreases along (g,h). -/
theorem p4Q2JX_originalPosteriorMinor_pos_of_temporal_lt
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (g h : Gauge) (hD : D g < D h) :
    0 < M b hb.le right e g h := by
  have hP : 0 <
      p4Q2JN_originalPosteriorIdentityDensity H b hb.le right e h *
        p4Q2JN_originalPosteriorPiDensity H b hb.le right e g :=
    mul_pos
      (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e h).1
      (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e g).2
  have hExponent : 0 < -b * (D g - D h) := by
    nlinarith [mul_pos hb (sub_pos.mpr hD)]
  have hExp : 1 < Real.exp (-b * (D g - D h)) := by
    simpa using (Real.exp_lt_exp.mpr hExponent)
  have hFactor : 0 < Real.exp (-b * (D g - D h)) - 1 := by
    linarith
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
  exact mul_pos hFactor hP

/-- The SAME original physical interacting posterior minor is strictly
negative when D(g)>D(h). The unknown Perron density factors remain
positive and cannot reverse the sign. -/
theorem p4Q2JX_originalPosteriorMinor_neg_of_temporal_gt
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (g h : Gauge) (hD : D h < D g) :
    M b hb.le right e g h < 0 := by
  have hP : 0 <
      p4Q2JN_originalPosteriorIdentityDensity H b hb.le right e h *
        p4Q2JN_originalPosteriorPiDensity H b hb.le right e g :=
    mul_pos
      (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e h).1
      (p4Q2JN_originalPosteriorDensity_pos H b hb.le right e g).2
  have hExponent : -b * (D g - D h) < 0 := by
    nlinarith [mul_pos hb (sub_pos.mpr hD)]
  have hExp : Real.exp (-b * (D g - D h)) < 1 := by
    simpa using (Real.exp_lt_exp.mpr hExponent)
  have hFactor : Real.exp (-b * (D g - D h)) - 1 < 0 := by
    linarith
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
  exact mul_neg_of_neg_of_pos hFactor hP

/-- Exact OPPOSITE ORDER for ALL actual SU(2) physical insertions.
This is pointwise and nonperturbative for every b>0. -/
theorem p4Q2JX_originalPosteriorMinor_temporalOrder_nonpos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (g h : Gauge) :
    M b hb.le right e g h * (D g - D h) ≤ 0 := by
  rcases lt_trichotomy (D g) (D h) with hlt | heq | hgt
  · have hm := p4Q2JX_originalPosteriorMinor_pos_of_temporal_lt
      H b hb right e g h hlt
    exact mul_nonpos_of_nonneg_of_nonpos hm.le (sub_nonpos.mpr hlt.le)
  · rw [heq, sub_self, mul_zero]
  · have hm := p4Q2JX_originalPosteriorMinor_neg_of_temporal_gt
      H b hb right e g h hgt
    exact mul_nonpos_of_nonpos_of_nonneg hm.le (sub_nonneg.mpr hgt.le)

/-- The original temporal physical receiver's test integral against
the difference of TWO true normalized interacting posteriors is EXACTLY
a double genuine SU(2) Haar integral of the original two-point minor.
No Fubini exchange or changed conditional law is required. -/
theorem p4Q2JX_originalPosteriorTestGap_eq_iteratedMinor
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e F =
      ∫ g : Gauge, ∫ h : Gauge,
        F g * M b hb right e g h ∂nu ∂nu := by
  change
    (∫ g : Gauge,
      F g * p4Q2GB_originalWilsonPosteriorLeftDensityContrast
        H b hb right e g ∂nu) = _
  apply integral_congr_ae
  filter_upwards with g
  rw [p4Q2JN2_originalDensityContrast_eq_minorHaarIntegral]
  rw [integral_const_mul]

/-- The SAME original posterior test integrated against the exact
temporal SU(2) exponential increment, retaining BOTH original
physical interacting posterior density factors. -/
theorem p4Q2JX_originalPosteriorTestGap_eq_iteratedExpKernel
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap H b hb right e F =
      ∫ g : Gauge, ∫ h : Gauge,
        F g *
          ((Real.exp (-b * (D g - D h)) - 1) *
            (p4Q2JN_originalPosteriorIdentityDensity H b hb right e h *
              p4Q2JN_originalPosteriorPiDensity H b hb right e g))
          ∂nu ∂nu := by
  rw [p4Q2JX_originalPosteriorTestGap_eq_iteratedMinor]
  apply integral_congr_ae
  filter_upwards with g
  apply integral_congr_ae
  filter_upwards with h
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]

/-- The LITERAL ORIGINAL two-posterior double SU(2) Haar moment of the
actual anchored SPATIAL Wilson Gauss-law Hilbert source at a second
physical boundary/link context. -/
noncomputable def p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  ∫ g : Gauge, ∫ h : Gauge,
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
      e' z' g *
    M b hb z'.2 e' g h ∂nu ∂nu

/-- Exactly the ORIGINAL spatial source's physical GI expectation
difference, including its untouched positive Perron/joint density
normalization. The inner conditional laws are BOTH interacting Wilson. -/
theorem p4Q2JX_originalSpatialSourcePhysicalGI_eq_doubleHaarMoment
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
      (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
      e' z' =
    -(p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment
      H b hb e e' z z') /
      p4Q2JQ_originalPhysicalGIDensityWeight H b hb z' := by
  rw [p4Q2JQ_originalGI_eq_originalPosteriorTemporalTestGap_div]
  rw [p4Q2JX_originalPosteriorTestGap_eq_iteratedMinor]
  rfl

/-- Actual spatial Wilson 2-context determinant represented by the
literal ORIGINAL SU(2) POSTERIOR DOUBLE HAAR integral, times only
the original nonzero physical anchor and original positive weight. -/
theorem p4Q2JX_originalSpatialMinor_eq_originalTwoPointMoment
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb e z
        (ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
          ℝ (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' =
      p4Q2JH_originalGIResponseCLM H b hb e z
        (ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
          ℝ (1 : C(Cfg, ℝ))) *
        (-(p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment
          H b hb e e' z z') /
            p4Q2JQ_originalPhysicalGIDensityWeight H b hb z') := by
  rw [p4Q2JU_originalSpatialMinor_eq_anchor_mul_physicalGI
    H b hb e e' z z' hAnchor]
  rw [p4Q2JX_originalSpatialSourcePhysicalGI_eq_doubleHaarMoment]

/-- The exact SAME original double-Haar moment, with the two-posterior
minor eliminated analytically in favor of the positive posterior
cross-density product and explicit temporal Wilson exponential increment.
This is a true original spatial-source kernel, not a surrogate detector. -/
theorem p4Q2JX_originalSpatialSourceDoubleMoment_eq_temporalExp
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment H b hb e e' z z' =
      ∫ g : Gauge, ∫ h : Gauge,
        p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
          e' z' g *
        ((Real.exp (-b * (D g - D h)) - 1) *
          (p4Q2JN_originalPosteriorIdentityDensity H b hb z'.2 e' h *
            p4Q2JN_originalPosteriorPiDensity H b hb z'.2 e' g))
        ∂nu ∂nu := by
  unfold p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment
  apply integral_congr_ae
  filter_upwards with g
  apply integral_congr_ae
  filter_upwards with h
  rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalPosteriorMinor_pos_of_temporal_lt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalPosteriorMinor_neg_of_temporal_gt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalPosteriorMinor_temporalOrder_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalPosteriorTestGap_eq_iteratedMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalPosteriorTestGap_eq_iteratedExpKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalSpatialSourcePhysicalGI_eq_doubleHaarMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalSpatialMinor_eq_originalTwoPointMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JX_originalSpatialSourceDoubleMoment_eq_temporalExp
