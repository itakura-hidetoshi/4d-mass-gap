import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroPointSpectrumLowerEdgeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- The real point spectrum of the normalized random-scan heat-bath operator on
the Gibbs-vacuum orthogonal sector. -/
def ContinuousCompactOrientedGaugeWilsonSystem.centeredRandomScanPointSpectrumL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Set ℝ :=
  {rho | ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ C.gibbsVacuumL2 f = 0 ∧
    C.randomScanHeatBathL2 f = rho • f}

/-- A centered random-scan Rayleigh upper bound controls every point-spectrum
value on the vacuum-orthogonal sector. -/
theorem continuous_compact_oriented_centeredRandomScanPointSpectrumL2_upper_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (rate : ℝ)
    (hRayleigh : ∀ f : Lp ℝ 2 C.gibbsMeasure,
      inner ℝ
          (C.randomScanHeatBathL2 (C.vacuumCenteredL2 f))
          (C.vacuumCenteredL2 f) ≤
        rate * ‖C.vacuumCenteredL2 f‖ ^ 2)
    {rho : ℝ}
    (hrho : rho ∈ C.centeredRandomScanPointSpectrumL2) :
    rho ≤ rate := by
  change ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ C.gibbsVacuumL2 f = 0 ∧
    C.randomScanHeatBathL2 f = rho • f at hrho
  rcases hrho with ⟨f, hf, hOrth, hEigen⟩
  have hBound := hRayleigh f
  rw [continuous_compact_oriented_vacuumCenteredL2_eq_self C f hOrth,
    hEigen, real_inner_smul_left, real_inner_self_eq_norm_sq] at hBound
  have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hNormSqPos : 0 < ‖f‖ ^ 2 := by positivity
  nlinarith

/-- The actual random-scan operator fixes the normalized Gibbs vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_vacuum :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
  have hEdge :
      0 < Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    norm_num
  exact continuous_compact_oriented_randomScanHeatBathL2_vacuum
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem hEdge

/-- The explicit unit one-link Hamiltonian eigenvector is a random-scan
eigenvector with eigenvalue exactly `323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_randomScan_eq_323_over_324_smul :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      ((323 : ℝ) / 324) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 := by
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  let q := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2
  have hEdge : 0 < Fintype.card C.base.geometry.Edge := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    norm_num
  have hHamiltonian : C.heatBathHamiltonianL2 q = q :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_hamiltonian_eq_self
  calc
    C.randomScanHeatBathL2 q =
        q - (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ •
          C.heatBathHamiltonianL2 q :=
      continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
        C hEdge q
    _ = q - (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ • q := by
      rw [hHamiltonian]
    _ = (1 - (Fintype.card C.base.geometry.Edge : ℝ)⁻¹) • q := by
      rw [sub_smul, one_smul]
    _ = (1 - 1 / (Fintype.card C.base.geometry.Edge : ℝ)) • q := by
      rw [one_div]
    _ = ((323 : ℝ) / 324) • q := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_randomScanRate_one_eq_323_over_324]

/-- The endpoint rate `323 / 324` belongs to the actual centered random-scan
point spectrum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_323_over_324_mem_centeredRandomScanPointSpectrumL2 :
    ((323 : ℝ) / 324) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 := by
  change ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f = 0 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
      ((323 : ℝ) / 324) • f
  refine ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2,
    ?_, ?_,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_randomScan_eq_323_over_324_smul⟩
  · intro hZero
    have hNorm :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one
    rw [hZero, norm_zero] at hNorm
    norm_num at hNorm
  · exact
      (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2).mp
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_mem_vacuumOrthogonal

/-- Every actual centered random-scan point-spectrum value is at most
`323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_le_323_over_324
    {rho : ℝ}
    (hrho : rho ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2) :
    rho ≤ (323 : ℝ) / 324 :=
  continuous_compact_oriented_centeredRandomScanPointSpectrumL2_upper_bound
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    ((323 : ℝ) / 324)
    periodicHypercubicThreeSpecialUnitaryTwoEndpointCenteredRandomScanRayleigh323Over324_proved
    hrho

/-- The exact endpoint rate is the greatest centered random-scan point-spectrum
value of the actual beta-zero system. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_isGreatest_323_over_324 :
    IsGreatest
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2
      ((323 : ℝ) / 324) := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_323_over_324_mem_centeredRandomScanPointSpectrumL2,
    fun _ hrho =>
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_le_323_over_324
        hrho⟩

/-- The supremum of the actual centered random-scan point spectrum is exactly
`323 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_sSup_eq_323_over_324 :
    sSup
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 =
      (323 : ℝ) / 324 := by
  let S : Set ℝ :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2
  have hGreatest : IsGreatest S ((323 : ℝ) / 324) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_isGreatest_323_over_324
  have hBdd : BddAbove S :=
    ⟨(323 : ℝ) / 324, fun _ hrho => hGreatest.2 hrho⟩
  have hNonempty : S.Nonempty := ⟨(323 : ℝ) / 324, hGreatest.1⟩
  apply le_antisymm
  · exact csSup_le hNonempty (fun _ hrho => hGreatest.2 hrho)
  · exact le_csSup hBdd hGreatest.1

/-- Compact receipt for the actual finite-volume beta-zero random-scan
point-spectrum upper edge.  This is a point-spectrum statement and does not
assert compactness or discreteness of the full operator spectrum. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumUpperEdgeL2Receipt : Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 ∧
    IsGreatest
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2
      ((323 : ℝ) / 324) ∧
    sSup
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 =
      (323 : ℝ) / 324 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 =
      ((323 : ℝ) / 324) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2 ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.VacuumOrthogonalL2 ∧
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2‖ = 1

/-- The actual beta-zero random-scan point-spectrum upper-edge receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumUpperEdgeL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumUpperEdgeL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_vacuum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_isGreatest_323_over_324,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_sSup_eq_323_over_324,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_randomScan_eq_323_over_324_smul,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_mem_vacuumOrthogonal,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkUnitEigenvectorL2_norm_eq_one⟩

end

end MathlibAnalytic
end MGAP4D
