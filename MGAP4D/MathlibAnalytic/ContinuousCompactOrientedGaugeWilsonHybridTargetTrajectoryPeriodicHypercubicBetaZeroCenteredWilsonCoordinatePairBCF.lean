import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityTwoPairProfileL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFullCoordinateVacuumProjectionL2
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityTwoPairEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

local instance periodicCardinalityTwoSpecialUnitaryTwoIsTopologicalGroup :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance periodicCardinalityTwoSpecialUnitaryTwoCompactSpace :
    CompactSpace (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupCompactSpace 2

local instance periodicCardinalityTwoSpecialUnitaryTwoSecondCountableTopology :
    SecondCountableTopology (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance periodicCardinalityTwoSpecialUnitaryTwoMeasurableSpace :
    MeasurableSpace (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupMeasurableSpace 2

local instance periodicCardinalityTwoSpecialUnitaryTwoBorelSpace :
    BorelSpace (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupBorelSpace 2

/-- The normalized Haar mean of the rank-two Wilson energy. -/
noncomputable def specialUnitaryTwoWilsonEnergyHaarMean : ℝ :=
  ∫ g : SpecialUnitaryMatrixGroup 2,
    specialUnitaryWilsonPlaquetteEnergy 2 g
      ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)

/-- The centered rank-two Wilson energy read at an arbitrary physical edge. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ := by
  let f :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration → ℝ :=
    fun A =>
      specialUnitaryWilsonPlaquetteEnergy 2 (A edge) -
        specialUnitaryTwoWilsonEnergyHaarMean
  have hf : Continuous f := by
    exact
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        (continuous_apply edge)).sub continuous_const
  exact BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge A =
      specialUnitaryWilsonPlaquetteEnergy 2 (A edge) -
        specialUnitaryTwoWilsonEnergyHaarMean := by
  rfl

/-- A centered coordinate observable depends only on its selected physical
edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A B :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration)
    (hApply : A edge = B edge) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge A =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge B := by
  simp only [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    hApply]

/-- A centered coordinate observable is constant along every different
physical-link fiber. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
    (edge source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      source
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) := by
  intro A B hAgree
  apply
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
  exact hAgree edge (Ne.symm hSource)

/-- Haar averaging the centered coordinate observable in its own coordinate
gives zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) =
      fun _ => 0 := by
  funext A
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
      A]
  have hEnergyIntegrable :
      Integrable
        (fun g : SpecialUnitaryMatrixGroup 2 =>
          specialUnitaryWilsonPlaquetteEnergy 2 g)
        (normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)) := by
    exact
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    (∫ g : SpecialUnitaryMatrixGroup 2,
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
            A edge g)
        ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)) =
      ∫ g : SpecialUnitaryMatrixGroup 2,
        (specialUnitaryWilsonPlaquetteEnergy 2 g -
          specialUnitaryTwoWilsonEnergyHaarMean)
        ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2) := by
          apply integral_congr_ae
          filter_upwards [] with g
          simp [
            periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
            CompactOrientedGaugeWilsonSystem.replaceLink]
    _ =
      (∫ g : SpecialUnitaryMatrixGroup 2,
          specialUnitaryWilsonPlaquetteEnergy 2 g
          ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)) -
        ∫ _g : SpecialUnitaryMatrixGroup 2,
          specialUnitaryTwoWilsonEnergyHaarMean
          ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2) := by
            rw [integral_sub hEnergyIntegrable (integrable_const _)]
    _ = 0 := by
      simp [specialUnitaryTwoWilsonEnergyHaarMean]

/-- Haar averaging a centered coordinate observable in a different coordinate
fixes it. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_eq_self_of_ne
    (edge source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem source
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        edge source hSource)

/-- Product of two centered coordinate observables. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source A =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source A := by
  rfl

/-- The pair observable is nonzero whenever its two coordinates are distinct. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_ne_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source ≠ 0 := by
  intro hZero
  let A0 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    fun _ => 1
  let A1 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
        A0 target specialUnitaryTwoNegativeIdentity)
      source specialUnitaryTwoNegativeIdentity
  have hAt0 := congrArg
    (fun F : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      F A0)
    hZero
  have hAt1 := congrArg
    (fun F : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      F A1)
    hZero
  have hA1Target : A1 target = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink, hNe]
  have hA1Source : A1 source = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink]
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    A0] at hAt0
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    hA1Target, hA1Source] at hAt1
  have hAt0' :
      -specialUnitaryTwoWilsonEnergyHaarMean = 0 := by
    simpa only [specialUnitaryWilsonPlaquetteEnergy_two_one, zero_sub] using hAt0
  nlinarith

/-- A bounded continuous factor that is constant on the target fiber can be
pulled through the target-coordinate Haar average. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ)
    (hG : C.base.OffLinkFiberConstant target G)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathProjection target (F * G) A =
      C.singleLinkHeatBathProjection target F A * G A := by
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      C hBeta target (F * G) A,
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      C hBeta target F A]
  calc
    (∫ g : C.base.Gauge,
        (F * G) (C.base.replaceLink A target g)
        ∂normalizedCompactHaar C.base.Gauge) =
      ∫ g : C.base.Gauge,
        F (C.base.replaceLink A target g) * G A
        ∂normalizedCompactHaar C.base.Gauge := by
          apply integral_congr_ae
          filter_upwards [] with g
          have hAgree :
              C.base.AgreeOffLink
                (C.base.replaceLink A target g) A target := by
            intro edge hEdge
            simp [CompactOrientedGaugeWilsonSystem.replaceLink, hEdge]
          change
            F (C.base.replaceLink A target g) *
                G (C.base.replaceLink A target g) =
              F (C.base.replaceLink A target g) * G A
          rw [show G (C.base.replaceLink A target g) = G A from hG _ _ hAgree]
    _ =
      (∫ g : C.base.Gauge,
        F (C.base.replaceLink A target g)
        ∂normalizedCompactHaar C.base.Gauge) * G A := by
          rw [integral_mul_const]

/-- Averaging the pair observable in its first selected coordinate gives zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_target_eq_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source) =
      fun _ => 0 := by
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        source target hNe)
      A
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (fun B =>
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target B *
            periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source B)
        A = 0
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (fun B =>
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target B *
            periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source B)
        A =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          target
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target)
          A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source A
    at hMul
  rw [hMul]
  have hZero :=
    congrFun
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
        target)
      A
  rw [hZero, zero_mul]

/-- Averaging the pair observable in its second selected coordinate gives zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_source_eq_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source) =
      fun _ => 0 := by
  funext A
  have hComm :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          source target := by
    ext B
    simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
      mul_comm]
  rw [hComm]
  exact congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_target_eq_zero
      source target hNe.symm) A

/-- Every unselected coordinate projection fixes the pair observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_eq_self_of_ne
    (target source edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source := by
  apply
    continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source)
  intro A B hAgree
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply]
  congr 1
  · apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    exact hAgree target (Ne.symm hTarget)
  · apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    exact hAgree source (Ne.symm hSource)

end

end MathlibAnalytic
end MGAP4D
