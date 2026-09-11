import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicStrictCorrelationFactorBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- Positive native one-link conditional-pair energy forces a positive squared
heat-bath fluctuation norm. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_fluctuation_norm_sq_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < ‖C.singleLinkHeatBathFluctuationL2 target
      (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_two_mul_norm_sq]
    at hNative
  nlinarith

/-- Positive native one-link energy therefore gives a genuinely nonzero local
heat-bath projection defect in Gibbs `L²`. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_fluctuation_ne_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.singleLinkHeatBathFluctuationL2 target
      (C.gibbsL2RepresentativeBCF O) ≠ 0 := by
  intro hZero
  have hSq :=
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_fluctuation_norm_sq_pos
      C target O hNative
  simpa [hZero] using hSq

/-- One positive native link energy makes the sum of all native link energies
strictly positive. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_sum_native_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < ∑ edge : C.base.geometry.Edge,
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF edge O := by
  classical
  exact lt_of_lt_of_le hNative
    (Finset.single_le_sum
      (fun edge _ =>
        continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_nonneg
          C edge O)
      (Finset.mem_univ target))

/-- Hence one positive native link energy already makes the finite-volume
heat-bath Hamiltonian quadratic form strictly positive on the observable. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_hamiltonian_quadratic_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < inner ℝ
      (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
      (C.gibbsL2RepresentativeBCF O) := by
  have hSum :=
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_sum_native_pos
      C target O hNative
  have hEq :=
    continuous_compact_oriented_sum_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_two_mul_hamiltonian
      C O
  nlinarith

/-- One positive target endpoint conditional-variance gap makes the sum of all
target endpoint gaps strictly positive. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_implies_total_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hGap :
      0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF
  exact lt_of_lt_of_le hGap
    (Finset.single_le_sum
      (fun edge _ =>
        continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_nonneg
          C edge O)
      (Finset.mem_univ target))

/-- The actual periodic six-plaquette observable has a positive squared local
heat-bath fluctuation norm at the distinguished target link. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fluctuation_norm_sq_pos :
    0 < ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF)‖ ^ 2 := by
  exact
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_fluctuation_norm_sq_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- Its local heat-bath projection defect is therefore nonzero in Gibbs `L²`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fluctuation_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF) ≠ 0 := by
  exact
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_fluctuation_ne_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- The sum of all native one-link energies is strictly positive for the actual
periodic observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_sum_native_pos :
    0 < ∑ target :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
        target periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_sum_native_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- The actual bounded-continuous observable has strictly positive finite-volume
heat-bath Hamiltonian quadratic form. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_hamiltonian_quadratic_pos :
    0 < inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF))
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF) := by
  exact
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_pos_implies_hamiltonian_quadratic_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

/-- The full finite sum of endpoint conditional-variance gaps is strictly positive
for the actual periodic observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_total_gap_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_implies_total_gap_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_globalGap_pos_of_lowerBound_six

/-- The exact all-target endpoint correlation ratio for the actual finite-volume
observable is strictly below one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_total_correlationRatio_lt_one :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF < 1 := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF_lt_one_iff_total_gap_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_sum_native_pos).2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_total_gap_pos

/-- Thus the summed endpoint cross moment admits some strict scalar factor below
one against the summed native energy.  The factor remains existential and
finite-volume specific. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_exists_total_strict_correlation_factor :
    ∃ ρ : ℝ, ρ < 1 ∧
      (∑ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF) ≤
        ρ * ∑ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
            target periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_pos_iff_exists_strict_correlation_factor
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_sum_native_pos).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_total_gap_pos

/-- The exact total correlation ratio itself is a canonical strict-factor witness
and recovers the summed endpoint cross moment after multiplication by summed
native energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_total_correlationRatio_witness :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF < 1 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF *
        (∑ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
            target periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF) =
      ∑ target :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  refine ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_total_correlationRatio_lt_one, ?_⟩
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF_mul_sum_native_eq_sum_cross
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_sum_native_pos

end

end MathlibAnalytic
end MGAP4D
