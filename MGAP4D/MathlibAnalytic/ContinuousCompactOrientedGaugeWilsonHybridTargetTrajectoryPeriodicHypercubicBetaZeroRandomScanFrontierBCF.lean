import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHomogeneousPoincareCoercivityBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryExplicitDobrushinL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

local instance periodicBetaZeroFrontierSpecialUnitaryTwoNontrivial :
    Nontrivial (SpecialUnitaryMatrixGroup 2) :=
  ⟨⟨specialUnitaryTwoNegativeIdentity, 1,
    specialUnitaryTwoNegativeIdentity_ne_one⟩⟩

/-- The side-three periodic four-dimensional physical-link set has exactly
`4 * 3^4 = 324` links. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324 :
    Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =
      324 := by
  change Fintype.card (PeriodicHypercubicEdge 3) = 324
  native_decide

/-- At zero Wilson coupling, the explicit compact-Haar `SU(N)` influence value
vanishes. -/
@[simp]
theorem periodicHypercubicSpecialUnitaryDobrushinEta_zero :
    periodicHypercubicSpecialUnitaryDobrushinEta 0 = 0 := by
  simp [periodicHypercubicSpecialUnitaryDobrushinEta,
    compactHaarOscillationInfluence,
    HaarLikelihoodRatioInfluence.coefficient]

/-- Hence the explicit unnormalized Dobrushin heat-bath gap at zero coupling is
exactly one. -/
@[simp]
theorem periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap_zero :
    periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap 0 = 1 := by
  simp [periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap,
    continuousCompactOrientedDobrushinHeatBathGap]

/-- Zero coupling lies strictly inside the explicit logarithmic Dobrushin
region. -/
theorem periodicHypercubicSpecialUnitary_zero_lt_log_dobrushin_threshold :
    (0 : ℝ) < Real.log ((19 : ℝ) / 17) / 4 := by
  have hRatio : (1 : ℝ) < (19 : ℝ) / 17 := by
    norm_num
  exact div_pos (Real.log_pos hRatio) (by norm_num)

/-- The actual zero-coupling side-three random-scan Rayleigh frontier, written
with the completely explicit rate `323 / 324`.  This is the one remaining
Hilbert-space estimate needed by the already constructed compact-Haar
Dobrushin matrix. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324 :
    Prop :=
  ∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.vacuumCenteredL2 f))
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.vacuumCenteredL2 f) ≤
      ((323 : ℝ) / 324) *
        ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.vacuumCenteredL2 f‖ ^ 2

/-- At the actual zero-coupling endpoint system, the abstract Dobrushin
random-scan rate simplifies exactly to `323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_dobrushinRandomScanRate_zero :
    continuousCompactOrientedDobrushinRandomScanRate
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        (18 * periodicHypercubicSpecialUnitaryDobrushinEta 0) =
      (323 : ℝ) / 324 := by
  rw [periodicHypercubicSpecialUnitaryDobrushinEta_zero]
  norm_num [continuousCompactOrientedDobrushinRandomScanRate,
    continuousCompactOrientedDobrushinHeatBathGap,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]

/-- The explicit `323/324` inequality is exactly the single analytic datum
consumed by the existing periodic compact-Haar `SU(2)` Dobrushin bridge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_iff_data :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324 ↔
      PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
        3 2 (by norm_num) 0 (by norm_num) := by
  constructor
  · intro hRayleigh
    refine
      { centered_randomScan_rayleigh_le := ?_ }
    intro f
    have h := hRayleigh f
    simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_dobrushinRandomScanRate_zero]
      using h
  · intro R f
    have h := R.centered_randomScan_rayleigh_le f
    simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_dobrushinRandomScanRate_zero]
      using h

/-- The explicit centered random-scan estimate yields the standard actual
heat-bath Poincare inequality with the numerical constant `1`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_one_of_centeredRandomScanRayleigh323Over324
    (hRayleigh :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 1 := by
  let R : PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
      3 2 (by norm_num) 0 (by norm_num) :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_iff_data).1
      hRayleigh
  have hPoincare :=
    periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathPoincareL2
      3 2 (by norm_num) (by norm_num) 0 (by norm_num)
      periodicHypercubicSpecialUnitary_zero_lt_log_dobrushin_threshold R
  simpa [periodicHypercubicSpecialUnitaryHeatBathPoincareL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem] using hPoincare

/-- The same explicit random-scan estimate gives homogeneous coercivity with
constant one on every actual vacuum-orthogonal vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoerciveAt_one_of_centeredRandomScanRayleigh323Over324
    (hRayleigh :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHeatBathCoerciveAtL2 1 := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoerciveAt_iff_poincare
      1).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_one_of_centeredRandomScanRayleigh323Over324
        hRayleigh)

/-- Consequently the actual finite-volume unit-sector Rayleigh infimum is at
least one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_one_le_rayleighInfimum_of_centeredRandomScanRayleigh323Over324
    (hRayleigh :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324) :
    1 ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_le_rayleighInfimum
      1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_one_of_centeredRandomScanRayleigh323Over324
        hRayleigh)

/-- Thus the explicit `323/324` random-scan estimate implies strict positivity
of the actual finite-volume variational lower edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_of_centeredRandomScanRayleigh323Over324
    (hRayleigh :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324) :
    0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum := by
  exact lt_of_lt_of_le zero_lt_one
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_one_le_rayleighInfimum_of_centeredRandomScanRayleigh323Over324
      hRayleigh)

/-- The same single analytic inequality therefore excludes approximate common
off-link fixed unit vectors by a uniform positive separation constant. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_offLinkUniformSeparation_of_centeredRandomScanRayleigh323Over324
    (hRayleigh :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_offLinkUniformSeparation).1
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_of_centeredRandomScanRayleigh323Over324
        hRayleigh)

/-- Compact receipt for the actual zero-coupling random-scan frontier.  The
receipt is conditional only on the displayed `323/324` centered Rayleigh
inequality; no spectral or continuum conclusion is asserted. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanFrontierReceipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324 →
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 1 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHeatBathCoerciveAtL2 1 ∧
      1 ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2

/-- The actual zero-coupling frontier receipt follows from the existing explicit
Dobrushin matrix bridge and the new specialization lemmas. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanFrontierReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanFrontierReceipt := by
  intro hRayleigh
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_poincare_one_of_centeredRandomScanRayleigh323Over324
      hRayleigh,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoerciveAt_one_of_centeredRandomScanRayleigh323Over324
      hRayleigh,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_one_le_rayleighInfimum_of_centeredRandomScanRayleigh323Over324
      hRayleigh,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_offLinkUniformSeparation_of_centeredRandomScanRayleigh323Over324
      hRayleigh⟩

end

end MathlibAnalytic
end MGAP4D