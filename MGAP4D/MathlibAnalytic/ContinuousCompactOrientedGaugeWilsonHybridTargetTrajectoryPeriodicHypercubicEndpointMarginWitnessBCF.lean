import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicSixStapleEndpointRealizationBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryLaw
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance periodicEndpointSpecialUnitaryTwoIsTopologicalGroup :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance periodicEndpointSpecialUnitaryTwoCompactSpace :
    CompactSpace (SpecialUnitaryMatrixGroup 2) :=
  specialUnitaryGroupCompactSpace 2

local instance periodicEndpointSpecialUnitaryTwoNontrivial :
    Nontrivial (SpecialUnitaryMatrixGroup 2) :=
  ⟨⟨specialUnitaryTwoNegativeIdentity, 1,
    specialUnitaryTwoNegativeIdentity_ne_one⟩⟩

private theorem periodicEndpoint_three_ge_two : 2 ≤ 3 := by
  norm_num

private theorem periodicEndpoint_two_pos : 0 < 2 := by
  norm_num

private theorem periodicEndpoint_beta_nonneg : 0 ≤ (0 : ℝ) := by
  norm_num

/-- The concrete side-three `SU(2)` Wilson system used by the endpoint witness. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  periodicHypercubicSpecialUnitaryWilsonSystem
    3 2 periodicEndpoint_two_pos 0 periodicEndpoint_beta_nonneg

local instance periodicEndpointSystemT2Space :
    T2Space periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge := by
  change T2Space (SpecialUnitaryMatrixGroup 2)
  infer_instance

/-- The one concrete configuration pair whose canonical hybrid path starts at the
identity configuration and ends at the far-side center configuration. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointPair :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  (periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration)

/-- The one named six-incidence family used by every endpoint statement below. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointIncidence
    (data : PeriodicHypercubicOtherAxis
      periodicHypercubicThreeOriginAxisZeroTarget.2 × Bool) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.IsolatedTargetPlaquetteIncidence
      periodicHypercubicThreeOriginAxisZeroTarget :=
  periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
    3 2 periodicEndpoint_three_ge_two periodicEndpoint_two_pos
    0 periodicEndpoint_beta_nonneg
    periodicHypercubicThreeOriginAxisZeroTarget data

/-- The canonical hybrid path at rank zero is exactly the identity endpoint. -/
@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_hybrid_zero :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridConfiguration
        periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.1
        periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.2 0 =
      periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoEndpointPair,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem]

/-- The full-rank canonical hybrid path is exactly the far-side center endpoint. -/
@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_hybrid_card :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridConfiguration
        periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.1
        periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.2
        (Fintype.card
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) =
      periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointPair] using
    (continuous_compact_oriented_independentPairHybridConfiguration_card
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration
      periodicHypercubicThreeSpecialUnitaryTwoFarSideCenterConfiguration)

/-- The six actual complement staples at the rank-zero trajectory endpoint are
six identity staples. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_initialStapleFamily :
    (fun data =>
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointIncidence data).stapleValue
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridConfiguration
          periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.1
          periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.2 0)) =
      specialUnitaryTwoPeriodicSixSameStapleFamily := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_hybrid_zero]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointIncidence,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily,
    specialUnitaryTwoPeriodicSixSameStapleFamily] using
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_identityConfiguration

/-- The six actual complement staples at the full-rank trajectory endpoint are
three identity/negative-identity pairs. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_finalStapleFamily :
    (fun data =>
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointIncidence data).stapleValue
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridConfiguration
          periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.1
          periodicHypercubicThreeSpecialUnitaryTwoEndpointPair.2
          (Fintype.card
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge))) =
      specialUnitaryTwoPeriodicSixSplitStapleFamily := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_hybrid_card]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointIncidence,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily,
    specialUnitaryTwoPeriodicSixSplitStapleFamily] using
    periodicHypercubicThreeSpecialUnitaryTwoCanonicalStapleFamily_farSideCenterConfiguration

/-- On the specialized periodic `SU(2)` system, the generic compact-system
plaquette-energy BCF is the explicit rank-two Wilson-energy BCF. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_plaquetteEnergyBCF_eq :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.plaquetteEnergyBCF =
      specialUnitaryTwoWilsonEnergyBCF := by
  ext g
  rfl

/-- The actual six-plaquette observable used at the fixed physical target. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.isolatedTargetPlaquetteObservableBCF
    periodicHypercubicThreeOriginAxisZeroTarget
    periodicHypercubicThreeSpecialUnitaryTwoEndpointIncidence

/-- The endpoint insertion-profile oscillation margin of the actual periodic
six-plaquette observable is exactly twelve. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_eq_twelve :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair = 12 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
  rw [continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_oscillationMargin_eq]
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_initialStapleFamily,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_finalStapleFamily,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_plaquetteEnergyBCF_eq,
    specialUnitaryTwoPeriodicSixSameStaple_oscillation_eq_twelve,
    specialUnitaryTwoPeriodicSixSplitStaple_oscillation_eq_zero]
  norm_num

/-- The concrete actual periodic endpoint margin is strictly positive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_eq_twelve]
  norm_num

/-- The concrete actual periodic six-plaquette observable has a genuine
coordinate-update separation witness along this one canonical hybrid trajectory. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_coordinateUpdateWitness :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_oscillationMargin_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair).2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_pos

/-- The same positive margin produces a nonempty open innovation-region witness
for this fixed concrete configuration pair. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_openRegionWitness :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_implies_open_region_witness
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_pos

/-- The same positive margin forces a positive fixed-fiber conditional-variance
gap at the concrete periodic configuration pair. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberGap_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_implies_gap_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_pos

end

end MathlibAnalytic
end MGAP4D
