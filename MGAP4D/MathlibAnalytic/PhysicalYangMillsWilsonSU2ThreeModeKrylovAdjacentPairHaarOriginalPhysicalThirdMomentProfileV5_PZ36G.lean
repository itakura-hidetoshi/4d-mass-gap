import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSecondMomentProfileV5_PZ36F
import Mathlib.Tactic

/-!
# P4-Q2-PZ36G — original double Haar cubic moment and PZ23 beta2

The actual Q(Y,X,B)=S(Y,X)+S(X,B) is retained, with the COMPLETE
intermediate spatial Wilson action. Source PZ19's exact third Haar
polynomial and PZ23's concrete low Ward coefficient are identified
without any independent moment premise or altered posterior.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36G_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36G_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36G_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36G_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36G_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36G_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36G_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalTwoThirdMoment
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))
local notation "R1" => p4Q2PZ36D_originalOneRaw H
local notation "R2" => p4Q2PZ36D_originalTwoRaw H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "η3" => p4Q2PZ19_originalStrippedCubicHaarConstant H

/-- Original SU(2) one-slab third raw moment, no replacement measure. -/
theorem p4Q2PZ36G_originalRawThird_spatialCubic (X : Cfg) :
    R1 3 X = (w X)^3 + 3*α*(w X)^2 + 3*θ*w X + η3 := by
  simpa only [p4Q2PZ36D_originalOneRaw,
    p4Q2PZ16_originalLeftSlabMoment] using
      (p4Q2PZ19_originalCompleteThird_cubicSpatial H X)

theorem p4Q2PZ36G_originalRawThird_continuous :
    Continuous (fun X : Cfg => R1 3 X) := by
  have hw := p4Q2PZ36C_half_continuous H
  have heq : (fun X : Cfg => R1 3 X) =
      fun X : Cfg => (w X)^3 + 3*α*(w X)^2 + 3*θ*w X + η3 := by
    funext X
    exact p4Q2PZ36G_originalRawThird_spatialCubic H X
  rw [heq]
  fun_prop (disch := assumption)

/-- Every inner cubic sector comes from the genuine two-step action,
including the full middle Wilson plaquette energy. -/
theorem p4Q2PZ36G_originalTwoThird_inner (X B : Cfg) :
    (∫ Y : Cfg, (Q Y X B)^3 ∂haar) =
      R1 3 X + 3*(R1 2 X)*(S X B) +
        3*(R1 1 X)*(S X B)^2 + (S X B)^3 := by
  have hS := p4Q2PZ36F_originalSlabRow_continuous H X
  change (∫ Y : Cfg, (S Y X + S X B)^3 ∂haar) = _
  rw [p4Q2PZ36A_originalHaar_integral_binomial H
    (fun Y : Cfg => S Y X) (fun _ : Cfg => S X B)
    hS continuous_const 3]
  simp [Finset.sum_range_succ, Nat.choose,
    p4Q2PZ36D_originalOneRaw, integral_mul_const]
  ring

/-- No posterior or H-dependence assumptions; exact original
interacting two-slab cubic raw Haar at the identity endpoint. -/
theorem p4Q2PZ36G_originalTwoThird_identity_split :
    R2 3 I = R1 3 I +
      (∫ X : Cfg,
        R1 3 X + 3*(R1 2 X)*(S X I) +
          3*(R1 1 X)*(S X I)^2 ∂haar) := by
  have hS := p4Q2PZ36F_originalSlabRow_continuous H I
  have h1 := p4Q2PZ36F_originalRawFirst_continuous H
  have h2 := p4Q2PZ36F_originalRawSecond_continuous H
  have h3 := p4Q2PZ36G_originalRawThird_continuous H
  have hMix : Continuous
      (fun X : Cfg =>
        R1 3 X + 3*(R1 2 X)*(S X I) +
          3*(R1 1 X)*(S X I)^2) :=
    (h3.add ((continuous_const.mul h2).mul hS)).add
      ((continuous_const.mul h1).mul (hS.pow 2))
  calc
    R2 3 I =
        (∫ X : Cfg,
          (R1 3 X + 3*(R1 2 X)*(S X I) +
            3*(R1 1 X)*(S X I)^2) + (S X I)^3 ∂haar) := by
          unfold p4Q2PZ36D_originalTwoRaw
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ36G_originalTwoThird_inner H X I
    _ = (∫ X : Cfg,
            R1 3 X + 3*(R1 2 X)*(S X I) +
              3*(R1 1 X)*(S X I)^2 ∂haar) +
          (∫ X : Cfg, (S X I)^3 ∂haar) := by
          simpa only [Pi.add_apply] using
            (integral_add
              (hMix.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _))
              ((hS.pow 3).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)))
    _ = R1 3 I +
          (∫ X : Cfg,
            R1 3 X + 3*(R1 2 X)*(S X I) +
              3*(R1 1 X)*(S X I)^2 ∂haar) := by
      unfold p4Q2PZ36D_originalOneRaw
      ring

/-- PZ23's original low profile coefficient of y², pointwise, with
all original left, middle and right Wilson action sectors present. -/
theorem p4Q2PZ36G_originalLowCoeff2_integrand (X : Cfg) :
    p4Q2PZ23_originalLowCoeff2 H X =
      10*(R1 3 X + 3*(R1 2 X)*(S X I) +
        3*(R1 1 X)*(S X I)^2) := by
  rw [p4Q2PZ36G_originalRawThird_spatialCubic H X,
    p4Q2PZ36F_originalRawSecond_spatialQuadratic H X,
    p4Q2PZ36E_originalRawFirst_spatialAffine H X,
    p4Q2PZ36C_originalOneSlab_eq_rightStripped H X I,
    p4Q2PZ35_originalHalfSpatialAction_identity_zero H]
  unfold p4Q2PZ23_originalLowCoeff2
    p4Q2PZ22_originalM3 p4Q2PZ22_originalM2
    p4Q2PZ22_originalM1
  ring

/-- Original true SU(2) physical beta2 coefficient transport. -/
theorem p4Q2PZ36G_originalLowCoeffHaar2_eq_trueMomentDifference :
    p4Q2PZ23_originalLowCoeffHaar2 H =
      10*(R2 3 I - R1 3 I) := by
  calc
    p4Q2PZ23_originalLowCoeffHaar2 H =
        (∫ X : Cfg,
          10*(R1 3 X + 3*(R1 2 X)*(S X I) +
            3*(R1 1 X)*(S X I)^2) ∂haar) := by
          unfold p4Q2PZ23_originalLowCoeffHaar2
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ36G_originalLowCoeff2_integrand H X
    _ = 10*(∫ X : Cfg,
            R1 3 X + 3*(R1 2 X)*(S X I) +
              3*(R1 1 X)*(S X I)^2 ∂haar) := by
      rw [integral_const_mul]
    _ = 10*(R2 3 I - R1 3 I) := by
      rw [p4Q2PZ36G_originalTwoThird_identity_split H]
      ring

end OriginalTwoThirdMoment
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36G_originalRawThird_spatialCubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36G_originalRawThird_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36G_originalTwoThird_inner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36G_originalTwoThird_identity_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36G_originalLowCoeff2_integrand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36G_originalLowCoeffHaar2_eq_trueMomentDifference
