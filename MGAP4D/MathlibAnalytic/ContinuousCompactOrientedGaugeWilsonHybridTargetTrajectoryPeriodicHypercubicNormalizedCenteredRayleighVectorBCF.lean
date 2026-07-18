import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicCenteredRayleighWitnessBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

set_option maxRecDepth 8192

/-- Vacuum centering is orthogonal to the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_vacuumCentered_inner_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ C.gibbsVacuumL2 (C.vacuumCenteredL2 f) = 0 := by
  have hVacuumInner : inner ℝ C.gibbsVacuumL2 C.gibbsVacuumL2 = 1 := by
    rw [real_inner_self_eq_norm_sq,
      continuous_compact_oriented_gibbsVacuumL2_norm]
    norm_num
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [inner_sub_right, real_inner_smul_right, hVacuumInner]
  ring

/-- Normalize the centered Gibbs `L²` representative of a bounded-continuous
observable.  This definition is meaningful as a unit vector whenever the
centered representative is nonzero. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicNormalizedCenteredRayleighVectorBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Lp ℝ 2 C.gibbsMeasure :=
  let centered := C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)
  ‖centered‖⁻¹ • centered

/-- A nonzero centered representative normalizes to a unit Gibbs `L²` vector. -/
theorem continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_norm_eq_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hCentered :
      C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O) ≠ 0) :
    ‖C.periodicNormalizedCenteredRayleighVectorBCF O‖ = 1 := by
  let centered := C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)
  have hNormPos : 0 < ‖centered‖ := by
    exact norm_pos_iff.mpr (by simpa [centered] using hCentered)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicNormalizedCenteredRayleighVectorBCF
  change ‖‖centered‖⁻¹ • centered‖ = 1
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hNormPos)]
  exact inv_mul_cancel₀ (ne_of_gt hNormPos)

/-- The normalized centered representative remains orthogonal to the Gibbs
vacuum. -/
theorem continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_inner_vacuum_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    inner ℝ C.gibbsVacuumL2
      (C.periodicNormalizedCenteredRayleighVectorBCF O) = 0 := by
  let centered := C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicNormalizedCenteredRayleighVectorBCF
  change inner ℝ C.gibbsVacuumL2 (‖centered‖⁻¹ • centered) = 0
  rw [real_inner_smul_right,
    continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_vacuumCentered_inner_zero]
  ring

/-- On positive-variance observables, the Hamiltonian expectation of the
normalized centered vector is exactly the previously constructed centered
Rayleigh quotient. -/
theorem continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_quadratic_eq_quotient
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hVariance : 0 < C.gibbsVarianceBCF O) :
    inner ℝ
        (C.heatBathHamiltonianL2
          (C.periodicNormalizedCenteredRayleighVectorBCF O))
        (C.periodicNormalizedCenteredRayleighVectorBCF O) =
      C.periodicCenteredHeatBathRayleighWitnessBCF O := by
  let centered := C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)
  have hVarEq : C.gibbsVarianceBCF O = ‖centered‖ ^ 2 := by
    simpa [centered] using
      (continuous_compact_oriented_gibbsVarianceBCF_eq_vacuumCentered_norm_sq
        C O)
  have hNormSqPos : 0 < ‖centered‖ ^ 2 := by
    rw [← hVarEq]
    exact hVariance
  have hNormNe : ‖centered‖ ≠ 0 := by
    intro hZero
    rw [hZero] at hNormSqPos
    norm_num at hNormSqPos
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicNormalizedCenteredRayleighVectorBCF
    ContinuousCompactOrientedGaugeWilsonSystem.periodicCenteredHeatBathRayleighWitnessBCF
  change
    inner ℝ
        (C.heatBathHamiltonianL2 (‖centered‖⁻¹ • centered))
        (‖centered‖⁻¹ • centered) =
      inner ℝ (C.heatBathHamiltonianL2 centered) centered /
        C.gibbsVarianceBCF O
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, hVarEq]
  field_simp [hNormNe]
  ring

/-- Positive native energy makes the normalized centered vector a strictly
positive-energy finite-volume state. -/
theorem continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_nativeEnergy_pos_implies_quadratic_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < inner ℝ
      (C.heatBathHamiltonianL2
        (C.periodicNormalizedCenteredRayleighVectorBCF O))
      (C.periodicNormalizedCenteredRayleighVectorBCF O) := by
  have hVariance :=
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsVariance_pos
      C target O hNative
  rw [continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_quadratic_eq_quotient
    C O hVariance]
  exact
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_quotient_pos
      C target O hNative

abbrev periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicNormalizedCenteredRayleighVectorBCF
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF

/-- The actual periodic centered observable normalizes to a unit Gibbs `L²`
vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_norm_eq_one :
    ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF‖ = 1 := by
  exact
    continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_norm_eq_one
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centered_ne_zero

/-- The actual normalized centered vector lies in the Gibbs-vacuum orthogonal
sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_mem_vacuumOrthogonal :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.VacuumOrthogonalL2 := by
  apply
    (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF).2
  exact
    continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_inner_vacuum_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF

/-- The actual normalized centered vector has strictly positive heat-bath
Hamiltonian expectation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_quadratic_pos :
    0 < inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF := by
  exact
    continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_nativeEnergy_pos_implies_quadratic_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- Its Hamiltonian expectation is exactly the actual centered Rayleigh
quotient from the preceding theorem unit. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_quadratic_eq_rayleigh :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF]
    using
      (continuous_compact_oriented_periodicNormalizedCenteredRayleighVector_quadratic_eq_quotient
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_gibbsVariance_pos)

/-- One concrete unit vector in the actual finite-volume Gibbs-vacuum orthogonal
sector has strictly positive heat-bath Hamiltonian expectation, equal to the
previously constructed centered Rayleigh quotient. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCenteredRayleighVector_witness :
    ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF‖ = 1 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.VacuumOrthogonalL2 ∧
      0 < inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF ∧
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF)
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableNormalizedCenteredGibbsL2BCF =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF := by
  exact
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_norm_eq_one,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_mem_vacuumOrthogonal,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_quadratic_pos,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_normalizedCentered_quadratic_eq_rayleigh⟩

end

end MathlibAnalytic
end MGAP4D