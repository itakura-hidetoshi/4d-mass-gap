import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCoordinateProjectionTensorizationL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanFrontierBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanL2Structure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

local instance periodicBetaZeroRandomScanSpecialUnitaryTwoNontrivial :
    Nontrivial (SpecialUnitaryMatrixGroup 2) :=
  ⟨⟨specialUnitaryTwoNegativeIdentity, 1,
    specialUnitaryTwoNegativeIdentity_ne_one⟩⟩

/-- The beta-zero tensorization theorem packages as the native heat-bath
Poincare inequality with constant one. -/
theorem continuous_compact_oriented_heatBathPoincareL2_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0) :
    C.HeatBathPoincareL2 1 := by
  intro f
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2] using
    continuous_compact_oriented_heatBathPoincare_one_of_beta_eq_zero C hBeta f

/-- At zero coupling, exact coordinate tensorization gives the centered
random-scan Rayleigh estimate with rate `1 - 1 / |Edge|`. -/
theorem continuous_compact_oriented_centeredRandomScanRayleigh_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    ∀ f : Lp ℝ 2 C.gibbsMeasure,
      inner ℝ
          (C.randomScanHeatBathL2 (C.vacuumCenteredL2 f))
          (C.vacuumCenteredL2 f) ≤
        (1 - 1 / (Fintype.card C.base.geometry.Edge : ℝ)) *
          ‖C.vacuumCenteredL2 f‖ ^ 2 := by
  exact
    (ContinuousCompactRandomScanL2Structure.continuous_compact_oriented_randomScanRayleigh_iff_heatBathPoincareL2
      C hEdge 1).2
      (continuous_compact_oriented_heatBathPoincareL2_one_of_beta_eq_zero
        C hBeta)

/-- For the actual 324-link endpoint system, the generic beta-zero random-scan
rate is exactly `323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_randomScanRate_one_eq_323_over_324 :
    1 - 1 /
        (Fintype.card
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge : ℝ) =
      (323 : ℝ) / 324 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
  norm_num

/-- The actual side-three periodic `SU(2)` beta-zero endpoint system satisfies
the explicit centered random-scan Rayleigh inequality with rate `323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324 := by
  intro f
  have hEdge :
      0 < Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    norm_num
  have hRayleigh :=
    continuous_compact_oriented_centeredRandomScanRayleigh_one_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      hEdge f
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_randomScanRate_one_eq_323_over_324]
    at hRayleigh
  exact hRayleigh

/-- The actual beta-zero endpoint system therefore satisfies the native
heat-bath Poincare inequality with constant one without any remaining analytic
hypothesis. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincareL2_one :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 1 :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_one_of_centeredRandomScanRayleigh323Over324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved

/-- The corresponding homogeneous heat-bath coercivity estimate with constant
one is unconditional for the actual beta-zero endpoint system. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_homogeneousHeatBathCoerciveAtL2_one :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHeatBathCoerciveAtL2 1 :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoerciveAt_one_of_centeredRandomScanRayleigh323Over324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved

/-- The actual finite-volume vacuum-orthogonal unit Rayleigh infimum is at
least one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_le_rayleighInfimum :
    1 ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_one_le_rayleighInfimum_of_centeredRandomScanRayleigh323Over324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved

/-- Hence the actual finite-volume variational lower edge is strictly positive.
This statement does not assert attainment of the infimum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_pos :
    0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_of_centeredRandomScanRayleigh323Over324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved

/-- The actual vacuum-orthogonal unit sector has unconditional uniform
separation from simultaneous off-link fixedness. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_offLinkUniformSeparation :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_offLinkUniformSeparation_of_centeredRandomScanRayleigh323Over324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved

/-- Compact receipt for closure of the actual beta-zero random-scan frontier.
It records the exact `323/324` Rayleigh estimate and its finite-volume
consequences, but does not assert infimum attainment, a discrete spectral gap,
volume uniformity, nonzero-beta control, a continuum limit, or a Yang--Mills
mass gap. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRayleighL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 1 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHeatBathCoerciveAtL2 1 ∧
    1 ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
    0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2

/-- The actual beta-zero random-scan Rayleigh receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRayleighL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRayleighL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincareL2_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_homogeneousHeatBathCoerciveAtL2_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_le_rayleighInfimum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rayleighInfimum_pos,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_offLinkUniformSeparation⟩

end

end MathlibAnalytic
end MGAP4D