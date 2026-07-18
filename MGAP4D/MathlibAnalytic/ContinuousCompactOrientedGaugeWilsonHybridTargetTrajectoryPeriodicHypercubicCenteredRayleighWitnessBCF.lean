import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHamiltonianTotalStrictCorrelationBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsPairVarianceBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

set_option maxRecDepth 2048

/-- A nonzero local heat-bath fluctuation forces the Gibbs-vacuum-centered
component of the original `L²` vector to be nonzero. -/
theorem continuous_compact_oriented_periodicCenteredRayleighWitness_fluctuation_ne_zero_implies_centered_ne_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hFluctuation : C.singleLinkHeatBathFluctuationL2 target f ≠ 0) :
    C.vacuumCenteredL2 f ≠ 0 := by
  intro hCentered
  have hScalar :
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2 at hCentered
    exact sub_eq_zero.mp hCentered
  apply hFluctuation
  rw [hScalar, map_smul,
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_vacuum]
  simp

/-- Positive native one-link conditional-pair energy forces strictly positive
Gibbs variance of the bounded-continuous observable. -/
theorem continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsVariance_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < C.gibbsVarianceBCF O := by
  have hFluctuation :
      C.singleLinkHeatBathFluctuationL2 target
          (C.gibbsL2RepresentativeBCF O) ≠ 0 :=
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_fluctuation_ne_zero
      C target O hNative
  have hCentered :
      C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O) ≠ 0 :=
    continuous_compact_oriented_periodicCenteredRayleighWitness_fluctuation_ne_zero_implies_centered_ne_zero
      C target (C.gibbsL2RepresentativeBCF O) hFluctuation
  rw [continuous_compact_oriented_gibbsVarianceBCF_eq_vacuumCentered_norm_sq]
  have hNorm :
      0 < ‖C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)‖ :=
    norm_pos_iff.mpr hCentered
  nlinarith

/-- The same positive native one-link energy gives a positive mean-square
difference under two independent full Gibbs configurations. -/
theorem continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsPairDifference_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < C.gibbsIndependentPairDifferenceEnergyBCF O := by
  have hVariance :=
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsVariance_pos
      C target O hNative
  rw [continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_eq_two_mul_variance]
  nlinarith

/-- Removing the Gibbs-vacuum component leaves the heat-bath Hamiltonian
quadratic form unchanged because the Hamiltonian annihilates the vacuum. -/
theorem continuous_compact_oriented_periodicCenteredRayleighWitness_vacuumCentered_quadraticForm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ
        (C.heatBathHamiltonianL2 (C.vacuumCenteredL2 f))
        (C.vacuumCenteredL2 f) =
      inner ℝ (C.heatBathHamiltonianL2 f) f := by
  let a : ℝ := inner ℝ C.gibbsVacuumL2 f
  have hVacuum : C.heatBathHamiltonianL2 C.gibbsVacuumL2 = 0 :=
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum C
  have hCross :
      inner ℝ (C.heatBathHamiltonianL2 f) C.gibbsVacuumL2 = 0 := by
    rw [continuous_compact_oriented_heatBathHamiltonianL2_inner_symm,
      hVacuum]
    simp
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  change
    inner ℝ
        (C.heatBathHamiltonianL2 (f - a • C.gibbsVacuumL2))
        (f - a • C.gibbsVacuumL2) =
      inner ℝ (C.heatBathHamiltonianL2 f) f
  calc
    inner ℝ
        (C.heatBathHamiltonianL2 (f - a • C.gibbsVacuumL2))
        (f - a • C.gibbsVacuumL2) =
      inner ℝ (C.heatBathHamiltonianL2 f)
        (f - a • C.gibbsVacuumL2) := by
          rw [map_sub, map_smul, hVacuum]
          simp
    _ = inner ℝ (C.heatBathHamiltonianL2 f) f := by
      rw [inner_sub_right, real_inner_smul_right, hCross]
      ring

/-- Centered finite-volume heat-bath Rayleigh quotient of a bounded-continuous
observable.  Its denominator is the exact Gibbs variance. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicCenteredHeatBathRayleighWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  let centered := C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)
  inner ℝ (C.heatBathHamiltonianL2 centered) centered /
    C.gibbsVarianceBCF O

/-- Positive native one-link energy produces a strictly positive centered
finite-volume Rayleigh quotient for that observable. -/
theorem continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_quotient_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < C.periodicCenteredHeatBathRayleighWitnessBCF O := by
  have hVariance :=
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsVariance_pos
      C target O hNative
  have hQuadratic :=
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_hamiltonian_quadratic_pos
      C target O hNative
  have hCenteredQuadratic :
      0 < inner ℝ
        (C.heatBathHamiltonianL2
          (C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)))
        (C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)) := by
    rw [continuous_compact_oriented_periodicCenteredRayleighWitness_vacuumCentered_quadraticForm]
    exact hQuadratic
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicCenteredHeatBathRayleighWitnessBCF
  exact div_pos hCenteredQuadratic hVariance

/-- The centered Rayleigh quotient exactly recovers the centered Hamiltonian
quadratic form after multiplication by the positive Gibbs variance. -/
theorem continuous_compact_oriented_periodicCenteredRayleighWitness_quotient_mul_variance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hVariance : 0 < C.gibbsVarianceBCF O) :
    C.periodicCenteredHeatBathRayleighWitnessBCF O * C.gibbsVarianceBCF O =
      inner ℝ
        (C.heatBathHamiltonianL2
          (C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)))
        (C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.periodicCenteredHeatBathRayleighWitnessBCF
  exact div_mul_cancel₀ _ (ne_of_gt hVariance)

abbrev periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF

abbrev periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredGibbsL2BCF :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.vacuumCenteredL2
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF

abbrev periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF : ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicCenteredHeatBathRayleighWitnessBCF
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF

/-- The actual periodic six-plaquette observable has a nonzero Gibbs-vacuum-
centered representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centered_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredGibbsL2BCF ≠ 0 := by
  exact
    continuous_compact_oriented_periodicCenteredRayleighWitness_fluctuation_ne_zero_implies_centered_ne_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fluctuation_ne_zero

/-- Its exact finite-volume Gibbs variance is strictly positive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_gibbsVariance_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVarianceBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsVariance_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- The mean-square observable difference for two independent Gibbs
configurations is strictly positive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_gibbsIndependentPairDifferenceEnergy_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsIndependentPairDifferenceEnergyBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_gibbsPairDifference_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- The centered finite-volume heat-bath Rayleigh quotient of the actual
periodic observable is strictly positive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF := by
  exact
    continuous_compact_oriented_periodicCenteredRayleighWitness_nativeEnergy_pos_implies_quotient_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- The positive centered Rayleigh quotient is an exact one-observable witness:
multiplied by Gibbs variance, it recovers the already-proved Hamiltonian
quadratic form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_witness :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF *
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVarianceBCF
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF =
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF)
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF := by
  refine
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_centeredRayleigh_pos, ?_⟩
  calc
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredRayleighBCF *
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVarianceBCF
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF =
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredGibbsL2BCF)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableCenteredGibbsL2BCF := by
      exact
        continuous_compact_oriented_periodicCenteredRayleighWitness_quotient_mul_variance
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_gibbsVariance_pos
    _ = inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF :=
      continuous_compact_oriented_periodicCenteredRayleighWitness_vacuumCentered_quadraticForm
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableGibbsL2BCF

end

end MathlibAnalytic
end MGAP4D
