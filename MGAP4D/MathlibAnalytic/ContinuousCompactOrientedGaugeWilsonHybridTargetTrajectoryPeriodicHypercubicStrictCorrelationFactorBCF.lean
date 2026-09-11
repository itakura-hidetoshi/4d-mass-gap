import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicIntegratedExcessMarginBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointStrictCorrelationRatioBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The double-trajectory endpoint energy is controlled by four times the native
one-link conditional-pair energy.  This is the elementary pointwise estimate
`(a - b)^2 ≤ 2 a^2 + 2 b^2`, integrated on the common double-trajectory law,
together with the exact native-energy identities at both endpoint ranks. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_four_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ≤
      4 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  let μ := C.independentPairHybridTargetTrajectoryDoubleJointMeasure target
  let n := Fintype.card C.base.geometry.Edge
  let D0 : C.independentPairHybridTargetTrajectoryDoubleJointCarrier → ℝ :=
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF target O 0
  let Dn : C.independentPairHybridTargetTrajectoryDoubleJointCarrier → ℝ :=
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF target O n
  have hD0 : Continuous D0 := by
    simpa [D0] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
        C target O 0
  have hDn : Continuous Dn := by
    simpa [Dn, n] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
        C target O (Fintype.card C.base.geometry.Edge)
  have hDouble : Integrable
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
        target O) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_integrable
        C target O
  have hD0Sq : Integrable (fun w => (D0 w) ^ 2) μ :=
    hD0.pow 2 |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDnSq : Integrable (fun w => (Dn w) ^ 2) μ :=
    hDn.pow 2 |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUpper : Integrable
      (fun w => 2 * (D0 w) ^ 2 + 2 * (Dn w) ^ 2) μ :=
    (hD0Sq.const_mul 2).add (hDnSq.const_mul 2)
  have hPoint (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O w ≤
        2 * (D0 w) ^ 2 + 2 * (Dn w) ^ 2 := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
    change (D0 w - Dn w) ^ 2 ≤ 2 * (D0 w) ^ 2 + 2 * (Dn w) ^ 2
    nlinarith [sq_nonneg (D0 w + Dn w)]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
  calc
    (∫ w,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O w ∂μ) ≤
      ∫ w, (2 * (D0 w) ^ 2 + 2 * (Dn w) ^ 2) ∂μ :=
        integral_mono hDouble hUpper hPoint
    _ = 2 * (∫ w, (D0 w) ^ 2 ∂μ) +
        2 * (∫ w, (Dn w) ^ 2 ∂μ) := by
      rw [integral_add (hD0Sq.const_mul 2) (hDnSq.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ = 2 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O +
        2 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
      rw [show (∫ w, (D0 w) ^ 2 ∂μ) =
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O by
        simpa [D0, μ] using
          continuous_compact_oriented_integral_doubleRankPairObservableBCF_zero_sq_eq_native
            C target O]
      rw [show (∫ w, (Dn w) ^ 2 ∂μ) =
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O by
        simpa [Dn, n, μ] using
          continuous_compact_oriented_integral_doubleRankPairObservableBCF_card_sq_eq_native
            C target O]
    _ = 4 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by ring

/-- Consequently the endpoint conditional-variance gap is at most twice the native
one-link conditional-pair energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_le_two_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O ≤
      2 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_half_double]
  have hDouble :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_four_native
      C target O
  nlinarith

/-- For the actual side-three periodic `SU(2)` six-plaquette observable, positivity
of the already-proved endpoint conditional-variance gap forces positivity of the
native one-link conditional-pair energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos :
    0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_globalGap_pos_of_lowerBound_six
  have hLe :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_le_two_native
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
  nlinarith

/-- The exact endpoint correlation ratio for the actual finite-volume periodic
observable is strictly below one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_correlationRatio_lt_one :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF < 1 := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_lt_one_iff_gap_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos).2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_globalGap_pos_of_lowerBound_six

/-- Hence the actual finite-volume endpoint cross moment admits some strict scalar
correlation factor `ρ < 1` against the native one-link energy.  The factor is
existential and is not claimed to be numerical or volume-uniform. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_exists_strict_correlation_factor :
    ∃ ρ : ℝ, ρ < 1 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          periodicHypercubicThreeOriginAxisZeroTarget
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF ≤
        ρ *
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_exists_strict_correlation_factor
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_globalGap_pos_of_lowerBound_six

/-- The exact correlation ratio itself is a canonical strict-factor witness and
recovers the actual cross moment after multiplication by the positive native
energy. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_correlationRatio_witness :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF < 1 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
          periodicHypercubicThreeOriginAxisZeroTarget
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF *
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
          periodicHypercubicThreeOriginAxisZeroTarget
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  refine ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_correlationRatio_lt_one, ?_⟩
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_mul_native_eq_cross
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_nativeEnergy_pos

end

end MathlibAnalytic
end MGAP4D
