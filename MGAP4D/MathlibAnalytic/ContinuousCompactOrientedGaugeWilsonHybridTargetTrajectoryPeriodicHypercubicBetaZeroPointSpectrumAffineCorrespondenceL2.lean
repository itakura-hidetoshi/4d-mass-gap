import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPointSpectrumUpperEdgeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open ContinuousCompactRandomScanL2Structure

noncomputable section

set_option maxRecDepth 8192

/-- For the actual 324-link beta-zero endpoint system, the Hamiltonian and
normalized random-scan eigenvector equations are exactly related by the affine
change of eigenvalue `rho = 1 - lam / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (lam : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        lam • f ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
        (1 - lam / 324) • f := by
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  have hEdge : 0 < Fintype.card C.base.geometry.Edge := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    norm_num
  constructor
  · intro hHamiltonian
    rw [continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
        C hEdge f,
      hHamiltonian,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324,
      smul_smul]
    have hScalar : (324 : ℝ)⁻¹ * lam = lam / 324 := by
      rw [div_eq_mul_inv]
      ring
    rw [hScalar, sub_smul, one_smul]
  · intro hRandomScan
    have hIdentity :=
      continuous_compact_oriented_randomScanHeatBathL2_eq_id_sub_hamiltonian
        C hEdge f
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
      at hIdentity
    have hInverseScaled :
        (324 : ℝ)⁻¹ • C.heatBathHamiltonianL2 f =
          (lam / 324) • f := by
      calc
        (324 : ℝ)⁻¹ • C.heatBathHamiltonianL2 f =
            f - C.randomScanHeatBathL2 f := by
          rw [hIdentity]
          abel
        _ = f - (1 - lam / 324) • f := by
          rw [hRandomScan]
        _ = (lam / 324) • f := by
          rw [sub_smul, one_smul]
          abel
    have hScaled := congrArg (fun x => (324 : ℝ) • x) hInverseScaled
    simpa [smul_smul, div_eq_mul_inv] using hScaled

/-- Every nonzero Hamiltonian point-spectrum value maps to a vacuum-orthogonal
random-scan point-spectrum value by `lam ↦ 1 - lam / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_nonzero_to_centeredRandomScanPointSpectrumL2
    {lam : ℝ}
    (hlam : lam ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ)) :
    (1 - lam / 324) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 := by
  change ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        lam • f at hlam
  rcases hlam.1 with ⟨f, hf, hHamiltonian⟩
  have hlamNe : lam ≠ 0 := by
    intro hZero
    apply hlam.2
    simpa [hZero]
  have hOrth :
      inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f = 0 :=
    continuous_compact_oriented_heatBathEigenvector_inner_vacuum_eq_zero_of_eigenvalue_ne_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      hlamNe hHamiltonian
  refine ⟨f, hf, hOrth, ?_⟩
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector
      f lam).mp hHamiltonian

/-- Every vacuum-orthogonal random-scan point-spectrum value maps back to a
nonzero Hamiltonian point-spectrum value by `rho ↦ 324 * (1 - rho)`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_to_nonzero_heatBathPointSpectrumL2
    {rho : ℝ}
    (hrho : rho ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2) :
    (324 : ℝ) * (1 - rho) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ) := by
  change ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f = 0 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
      rho • f at hrho
  rcases hrho with ⟨f, hf, hOrth, hRandomScan⟩
  have hAffine :
      1 - ((324 : ℝ) * (1 - rho)) / 324 = rho := by
    ring
  have hHamiltonian :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        ((324 : ℝ) * (1 - rho)) • f := by
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector
        f ((324 : ℝ) * (1 - rho))).mpr
    simpa [hAffine] using hRandomScan
  have hrhoLe : rho ≤ (323 : ℝ) / 324 :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_le_323_over_324
      ⟨f, hf, hOrth, hRandomScan⟩
  have hrhoLt : rho < 1 := by
    have hRateLt : (323 : ℝ) / 324 < 1 := by norm_num
    exact lt_of_le_of_lt hrhoLe hRateLt
  have hLamPos : 0 < (324 : ℝ) * (1 - rho) := by
    positivity
  refine ⟨⟨f, hf, hHamiltonian⟩, ?_⟩
  intro hZeroMem
  have hZero : (324 : ℝ) * (1 - rho) = 0 := by
    simpa using hZeroMem
  exact (ne_of_gt hLamPos) hZero

/-- The actual vacuum-orthogonal random-scan point spectrum is exactly the
image of the nonzero heat-bath Hamiltonian point spectrum under
`lam ↦ 1 - lam / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_eq_image_nonzero_heatBathPointSpectrumL2 :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 =
      Set.image
        (fun lam : ℝ => 1 - lam / 324)
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
          ({0} : Set ℝ)) := by
  ext rho
  constructor
  · intro hrho
    let lam : ℝ := (324 : ℝ) * (1 - rho)
    have hlam : lam ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
          ({0} : Set ℝ) := by
      dsimp [lam]
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_to_nonzero_heatBathPointSpectrumL2
          hrho
    refine ⟨lam, hlam, ?_⟩
    dsimp [lam]
    ring
  · rintro ⟨lam, hlam, rfl⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_nonzero_to_centeredRandomScanPointSpectrumL2
        hlam

/-- Conversely, the actual nonzero heat-bath Hamiltonian point spectrum is
exactly the image of the vacuum-orthogonal random-scan point spectrum under
`rho ↦ 324 * (1 - rho)`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_eq_image_centeredRandomScanPointSpectrumL2 :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ) =
      Set.image
        (fun rho : ℝ => (324 : ℝ) * (1 - rho))
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 := by
  ext lam
  constructor
  · intro hlam
    let rho : ℝ := 1 - lam / 324
    have hrho : rho ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 := by
      dsimp [rho]
      exact
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_nonzero_to_centeredRandomScanPointSpectrumL2
          hlam
    refine ⟨rho, hrho, ?_⟩
    dsimp [rho]
    ring
  · rintro ⟨rho, hrho, rfl⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_to_nonzero_heatBathPointSpectrumL2
        hrho

/-- Compact receipt for the exact affine correspondence between the actual
finite-volume beta-zero Hamiltonian nonzero point spectrum and the centered
random-scan point spectrum. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumAffineCorrespondenceL2Receipt : Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 =
      Set.image
        (fun lam : ℝ => 1 - lam / 324)
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
          ({0} : Set ℝ)) ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ) =
      Set.image
        (fun rho : ℝ => (324 : ℝ) * (1 - rho))
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 ∧
    ∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      ∀ lam : ℝ,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
            lam • f ↔
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
            (1 - lam / 324) • f

/-- The actual beta-zero point-spectrum affine-correspondence receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumAffineCorrespondenceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumAffineCorrespondenceL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_eq_image_nonzero_heatBathPointSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_eq_image_centeredRandomScanPointSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBath_eigenvector_iff_randomScan_eigenvector⟩

end

end MathlibAnalytic
end MGAP4D
