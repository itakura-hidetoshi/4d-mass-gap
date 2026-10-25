import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalCoefficientTransportV5_PZ36E
import Mathlib.Tactic

/-!
# P4-Q2-PZ36F — genuine two-slab second raw moment and low-profile beta3

Original Q(Y,X,B) = S(Y,X)+S(X,B), with full middle spatial action.
Identify PZ23's *actual* third quartic-profile coefficient with the
original SU(2) Haar two/one-slab second raw moments, without a postulate,
new posterior, replacement action or other source.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36F_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36F_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36F_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36F_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36F_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36F_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36F_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalTwoSecondMoment
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

theorem p4Q2PZ36F_originalRawSecond_spatialQuadratic (X : Cfg) :
    R1 2 X = (w X)^2 + 2*α*w X + θ := by
  simpa only [p4Q2PZ36D_originalOneRaw,
    p4Q2PZ16_originalLeftSlabMoment] using
      (p4Q2PZ17_originalSecondMoment_quadratic H X)

theorem p4Q2PZ36F_originalSlabRow_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hp : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using
    (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hp

theorem p4Q2PZ36F_originalRawSecond_continuous :
    Continuous (fun X : Cfg => R1 2 X) := by
  have hw := p4Q2PZ36C_half_continuous H
  have heq : (fun X : Cfg => R1 2 X) =
      fun X : Cfg => (w X)^2 + 2*α*w X + θ := by
    funext X
    exact p4Q2PZ36F_originalRawSecond_spatialQuadratic H X
  rw [heq]
  fun_prop (disch := assumption)

theorem p4Q2PZ36F_originalRawFirst_continuous :
    Continuous (fun X : Cfg => R1 1 X) := by
  have heq : (fun X : Cfg => R1 1 X) =
      fun X : Cfg => w X + α := by
    funext X
    exact p4Q2PZ36E_originalRawFirst_spatialAffine H X
  rw [heq]
  exact (p4Q2PZ36C_half_continuous H).add continuous_const

/-- No skipped intermediate action: binomial expansion is inside the
genuine left spatial SU(2) Haar integral for the literal Q. -/
theorem p4Q2PZ36F_originalTwoSecond_inner
    (X B : Cfg) :
    (∫ Y : Cfg, (Q Y X B)^2 ∂haar) =
      R1 2 X + 2*(R1 1 X)*(S X B) + (S X B)^2 := by
  have hS := p4Q2PZ36F_originalSlabRow_continuous H X
  change (∫ Y : Cfg, (S Y X + S X B)^2 ∂haar) = _
  rw [p4Q2PZ36A_originalHaar_integral_binomial H
    (fun Y : Cfg => S Y X) (fun _ : Cfg => S X B)
    hS continuous_const 2]
  simp [Finset.sum_range_succ, Nat.choose,
    p4Q2PZ36D_originalOneRaw, integral_mul_const]
  ring

/-- Full original physical double-Haar second raw moment, at the actual
zero-action identity boundary. -/
theorem p4Q2PZ36F_originalTwoSecond_identity_split :
    R2 2 I = R1 2 I +
      (∫ X : Cfg, R1 2 X + 2*(R1 1 X)*(S X I) ∂haar) := by
  have hS := p4Q2PZ36F_originalSlabRow_continuous H I
  have hR1 := p4Q2PZ36F_originalRawFirst_continuous H
  have hR2 := p4Q2PZ36F_originalRawSecond_continuous H
  have hMix : Continuous
      (fun X : Cfg => R1 2 X + 2*(R1 1 X)*(S X I)) :=
    hR2.add ((continuous_const.mul hR1).mul hS)
  calc
    R2 2 I =
        (∫ X : Cfg, (R1 2 X + 2*(R1 1 X)*(S X I)) + (S X I)^2 ∂haar) := by
          unfold p4Q2PZ36D_originalTwoRaw
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ36F_originalTwoSecond_inner H X I
    _ = (∫ X : Cfg, R1 2 X + 2*(R1 1 X)*(S X I) ∂haar) +
          (∫ X : Cfg, (S X I)^2 ∂haar) := by
          simpa only [Pi.add_apply] using
            (integral_add
              (hMix.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _))
              ((hS.pow 2).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)))
    _ = R1 2 I + (∫ X : Cfg, R1 2 X + 2*(R1 1 X)*(S X I) ∂haar) := by
      unfold p4Q2PZ36D_originalOneRaw
      ring

/-- Exact coefficient of y³ in PZ23's original true low Haar kernel,
pointwise on the SAME spatial SU(2) configuration. -/
theorem p4Q2PZ36F_originalLowCoeff3_integrand (X : Cfg) :
    p4Q2PZ23_originalLowCoeff3 H X =
      10*(R1 2 X + 2*(R1 1 X)*(S X I)) := by
  rw [p4Q2PZ36F_originalRawSecond_spatialQuadratic H X,
    p4Q2PZ36E_originalRawFirst_spatialAffine H X,
    p4Q2PZ36C_originalOneSlab_eq_rightStripped H X I,
    p4Q2PZ35_originalHalfSpatialAction_identity_zero H]
  unfold p4Q2PZ23_originalLowCoeff3
    p4Q2PZ22_originalM2 p4Q2PZ22_originalM1
  ring

/-- First previously missing actual original physical β₃ identity.
No independent coefficient-transport premise or algebraic substitution. -/
theorem p4Q2PZ36F_originalLowCoeffHaar3_eq_trueMomentDifference :
    p4Q2PZ23_originalLowCoeffHaar3 H =
      10*(R2 2 I - R1 2 I) := by
  calc
    p4Q2PZ23_originalLowCoeffHaar3 H =
        (∫ X : Cfg, 10*(R1 2 X + 2*(R1 1 X)*(S X I)) ∂haar) := by
          unfold p4Q2PZ23_originalLowCoeffHaar3
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ36F_originalLowCoeff3_integrand H X
    _ = 10*(∫ X : Cfg, R1 2 X + 2*(R1 1 X)*(S X I) ∂haar) := by
      rw [integral_const_mul]
    _ = 10*(R2 2 I - R1 2 I) := by
      rw [p4Q2PZ36F_originalTwoSecond_identity_split H]
      ring

end OriginalTwoSecondMoment
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalRawSecond_spatialQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalSlabRow_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalRawSecond_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalRawFirst_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalTwoSecond_inner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalTwoSecond_identity_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalLowCoeff3_integrand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36F_originalLowCoeffHaar3_eq_trueMomentDifference
