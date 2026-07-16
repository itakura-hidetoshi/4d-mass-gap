import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointCrossMomentFiberCovarianceBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsPairVarianceBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionL2Identification
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

private theorem continuous_compact_oriented_bcf_abs_le_norm_projection
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- Mean-square difference of the concrete one-link heat-bath projection on two
independent Gibbs configurations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z : C.base.Configuration × C.base.Configuration,
    (C.singleLinkHeatBathProjection target O z.1 -
      C.singleLinkHeatBathProjection target O z.2) ^ 2
    ∂(C.gibbsMeasure.prod C.gibbsMeasure)

/-- Gibbs variance of the concrete one-link heat-bath projection of a bounded
continuous observable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionVarianceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ProbabilityTheory.variance
    (C.singleLinkHeatBathProjection target O) C.gibbsMeasure

/-- The rank-zero trajectory endpoint mean on one fixed original Gibbs pair is
the one-link heat-bath projection evaluated at the left original configuration. -/
theorem continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF_eq_projection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    (∫ x,
      C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
        target O z x
      ∂C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)) =
      C.singleLinkHeatBathProjection target O z.1 := by
  let n := Fintype.card C.base.geometry.Edge
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target n
  let endpointMeasure :=
    C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
      target z
  let U :=
    C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
      target O z
  have hEndpointMap : Measurable
      (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap
        target z) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap_continuous
      C target z).measurable
  have hObsFst : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration => O y.1) :=
    (O.continuous.comp continuous_fst).stronglyMeasurable
  calc
    (∫ x, U x ∂trajectory) =
        ∫ y, O y.1 ∂endpointMeasure := by
      symm
      unfold endpointMeasure
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
      rw [MeasureTheory.integral_map hEndpointMap.aemeasurable
        hObsFst.aestronglyMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [U,
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF,
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap,
          continuous_compact_oriented_independentPairHybridConfiguration_zero]
    _ = ∫ A, O A ∂Measure.map Prod.fst endpointMeasure := by
      symm
      rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        O.continuous.stronglyMeasurable.aestronglyMeasurable]
    _ = ∫ A, O A ∂C.singleLinkHeatBathKernel target z.1 := by
      rw [show Measure.map Prod.fst endpointMeasure =
          C.singleLinkHeatBathKernel target z.1 by
        dsimp [endpointMeasure]
        exact
          continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
            C target z]
    _ = C.singleLinkHeatBathProjection target O z.1 := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
      rw [continuous_compact_oriented_singleLinkHeatBathKernel_apply]
      rw [MeasureTheory.integral_map
        (continuous_compact_oriented_replaceLink C z.1 target).measurable.aemeasurable
        O.continuous.stronglyMeasurable.aestronglyMeasurable]

/-- The full-rank trajectory endpoint mean on one fixed original Gibbs pair is
the one-link heat-bath projection evaluated at the right original configuration. -/
theorem continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF_eq_projection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    (∫ x,
      C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
        target O z x
      ∂C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)) =
      C.singleLinkHeatBathProjection target O z.2 := by
  let n := Fintype.card C.base.geometry.Edge
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target n
  let endpointMeasure :=
    C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
      target z
  let V :=
    C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
      target O z
  have hEndpointMap : Measurable
      (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap
        target z) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap_continuous
      C target z).measurable
  have hObsSnd : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration => O y.2) :=
    (O.continuous.comp continuous_snd).stronglyMeasurable
  calc
    (∫ x, V x ∂trajectory) =
        ∫ y, O y.2 ∂endpointMeasure := by
      symm
      unfold endpointMeasure
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
      rw [MeasureTheory.integral_map hEndpointMap.aemeasurable
        hObsSnd.aestronglyMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [V,
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF,
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap,
          continuous_compact_oriented_independentPairHybridConfiguration_card]
    _ = ∫ A, O A ∂Measure.map Prod.snd endpointMeasure := by
      symm
      rw [MeasureTheory.integral_map measurable_snd.aemeasurable
        O.continuous.stronglyMeasurable.aestronglyMeasurable]
    _ = ∫ A, O A ∂C.singleLinkHeatBathKernel target z.2 := by
      rw [show Measure.map Prod.snd endpointMeasure =
          C.singleLinkHeatBathKernel target z.2 by
        dsimp [endpointMeasure]
        exact
          continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
            C target z]
    _ = C.singleLinkHeatBathProjection target O z.2 := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
      rw [continuous_compact_oriented_singleLinkHeatBathKernel_apply]
      rw [MeasureTheory.integral_map
        (continuous_compact_oriented_replaceLink C z.2 target).measurable.aemeasurable
        O.continuous.stronglyMeasurable.aestronglyMeasurable]

/-- Conditional mean endpoint transport on a fixed original Gibbs pair is exactly
the difference of the two concrete one-link heat-bath projections. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF_eq_projection_sub_projection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF
        target O z =
      C.singleLinkHeatBathProjection target O z.1 -
        C.singleLinkHeatBathProjection target O z.2 := by
  let n := Fintype.card C.base.geometry.Edge
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target n
  let U :=
    C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
      target O z
  let V :=
    C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
      target O z
  have hU : Integrable U trajectory :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF_continuous
      C target O z).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hV : Integrable V trajectory :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF_continuous
      C target O z).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF
  change (∫ x,
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
        target O n (z, x) ∂trajectory) = _
  calc
    (∫ x,
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
          target O n (z, x) ∂trajectory) =
      ∫ x, U x - V x ∂trajectory := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simpa [n, U, V] using
            continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_eq_fiber_initial_sub_final
              C target O z x
    _ = (∫ x, U x ∂trajectory) - ∫ x, V x ∂trajectory :=
      integral_sub hU hV
    _ = C.singleLinkHeatBathProjection target O z.1 -
        C.singleLinkHeatBathProjection target O z.2 := by
      rw [show (∫ x, U x ∂trajectory) =
          C.singleLinkHeatBathProjection target O z.1 by
        simpa [trajectory, n, U] using
          continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF_eq_projection
            C target O z]
      rw [show (∫ x, V x ∂trajectory) =
          C.singleLinkHeatBathProjection target O z.2 by
        simpa [trajectory, n, V] using
          continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF_eq_projection
            C target O z]

/-- The Gibbs average of the conditional-mean transport square is exactly the
independent-pair difference energy of the one-link heat-bath projection. -/
theorem continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_eq_projection_pair_energy
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ z : C.base.Configuration × C.base.Configuration,
      C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
        target O z
      ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      C.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
        target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF_eq_projection_sub_projection]

/-- The independent Gibbs-pair projection difference energy is twice the Gibbs
variance of the one-link heat-bath projection. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF_eq_two_mul_variance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
        target O =
      2 * C.singleLinkHeatBathProjectionVarianceBCF target O := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ : Measure C.base.Configuration := C.gibbsMeasure
  let M : ℝ := ‖O‖
  let P : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathProjection target O
  have hOStrong : StronglyMeasurable
      (O : C.base.Configuration → ℝ) := O.continuous.stronglyMeasurable
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hOBound : ∀ A, |O A| ≤ M := by
    intro A
    exact continuous_compact_oriented_bcf_abs_le_norm_projection O A
  have hPStrong : StronglyMeasurable P := by
    dsimp [P]
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
        C target O hOStrong
  have hPBound : ∀ A, |P A| ≤ M := by
    intro A
    dsimp [P]
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
        C target O hOStrong M hM0 hOBound A
  let hP : MemLp P 2 μ :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C P hPStrong M hM0 hPBound
  let diff : C.base.Configuration × C.base.Configuration → ℝ :=
    fun z => P z.1 - P z.2
  have hDiff : MemLp diff 2 (μ.prod μ) := by
    dsimp [diff]
    exact (hP.comp_fst μ).sub (hP.comp_snd μ)
  have hPInt : Integrable P μ := hP.integrable one_le_two
  have hMeanZero : ∫ z, diff z ∂(μ.prod μ) = 0 := by
    dsimp [diff]
    rw [integral_sub (hPInt.comp_fst μ) (hPInt.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  have hVarianceIntegral :
      ProbabilityTheory.variance diff (μ.prod μ) =
        ∫ z, (diff z) ^ 2 ∂(μ.prod μ) :=
    ProbabilityTheory.variance_of_integral_eq_zero
      hDiff.aemeasurable hMeanZero
  have hVarianceProd :=
    ProbabilityTheory.variance_add_prod (μ := μ) (ν := μ) hP hP.neg
  calc
    C.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
        target O =
      ProbabilityTheory.variance diff (μ.prod μ) := by
        unfold
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
        change (∫ z, (diff z) ^ 2 ∂(μ.prod μ)) = _
        exact hVarianceIntegral.symm
    _ = ProbabilityTheory.variance P μ +
        ProbabilityTheory.variance (fun A => -P A) μ := by
      simpa [diff, sub_eq_add_neg] using hVarianceProd
    _ = 2 * ProbabilityTheory.variance P μ := by
      rw [ProbabilityTheory.variance_fun_neg]
      ring
    _ = 2 * C.singleLinkHeatBathProjectionVarianceBCF target O := by
      rfl

/-- Orthogonal heat-bath decomposition of Gibbs variance: the variance of the
one-link projection is the original Gibbs variance minus the squared local
fluctuation norm. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionVarianceBCF_eq_gibbsVariance_sub_fluctuation_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionVarianceBCF target O =
      C.gibbsVarianceBCF O -
        ‖C.singleLinkHeatBathFluctuationL2 target
          (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ : Measure C.base.Configuration := C.gibbsMeasure
  let M : ℝ := ‖O‖
  let P : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathProjection target O
  have hOStrong : StronglyMeasurable
      (O : C.base.Configuration → ℝ) := O.continuous.stronglyMeasurable
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hOBound : ∀ A, |O A| ≤ M := by
    intro A
    exact continuous_compact_oriented_bcf_abs_le_norm_projection O A
  have hPStrong : StronglyMeasurable P := by
    dsimp [P]
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
        C target O hOStrong
  have hPBound : ∀ A, |P A| ≤ M := by
    intro A
    dsimp [P]
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
        C target O hOStrong M hM0 hOBound A
  let hO : MemLp O 2 μ :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C O hOStrong M hM0 hOBound
  let hP : MemLp P 2 μ :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C P hPStrong M hM0 hPBound
  let f : Lp ℝ 2 μ := C.gibbsL2RepresentativeBCF O
  let p : Lp ℝ 2 μ := C.singleLinkHeatBathProjectionL2 target f
  let q : Lp ℝ 2 μ := C.singleLinkHeatBathFluctuationL2 target f
  have hpRep : p = hP.toLp P := by
    dsimp [p, f]
    simpa [μ, P, hP,
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
      using
        (continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
          C target O hOStrong M hM0 hOBound)
  have hFnorm : ‖f‖ ^ 2 = ∫ A, (O A) ^ 2 ∂μ := by
    simpa [f, μ] using
      continuous_compact_oriented_gibbsL2RepresentativeBCF_norm_sq_eq_integral_sq
        C O
  have hPnorm : ‖p‖ ^ 2 = ∫ A, (P A) ^ 2 ∂μ := by
    rw [hpRep, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hP.coeFn_toLp] with A hA
    rw [hA]
    simp [pow_two]
  have hMean : ∫ A, P A ∂μ = ∫ A, O A ∂μ := by
    dsimp [P, μ]
    exact
      continuous_compact_oriented_integral_singleLinkHeatBathProjection_eq
        C target O hOStrong M hM0 hOBound
  have hPq : C.singleLinkHeatBathProjectionL2 target q = 0 := by
    dsimp [q]
    rw [map_sub,
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]
    exact sub_self _
  have hpq : inner ℝ p q = 0 := by
    calc
      inner ℝ p q =
          inner ℝ f (C.singleLinkHeatBathProjectionL2 target q) := by
        simpa [p] using
          continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm
            C target f q
      _ = 0 := by rw [hPq, inner_zero_right]
  have hqp : inner ℝ q p = 0 := by
    rw [real_inner_comm]
    exact hpq
  have hDecomp : f = p + q := by
    dsimp [p, q]
    abel
  have hPythagoras : ‖f‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    calc
      ‖f‖ ^ 2 = inner ℝ f f :=
        (real_inner_self_eq_norm_sq f).symm
      _ = inner ℝ (p + q) (p + q) := by rw [hDecomp]
      _ = inner ℝ p p + inner ℝ q q := by
        simp only [inner_add_left, inner_add_right]
        rw [hpq, hqp]
        ring
      _ = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionVarianceBCF
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsVarianceBCF
  rw [ProbabilityTheory.variance_eq_sub hP,
    ProbabilityTheory.variance_eq_sub hO]
  change (∫ A, (P A) ^ 2 ∂μ) - (∫ A, P A ∂μ) ^ 2 =
    (∫ A, (O A) ^ 2 ∂μ) - (∫ A, O A ∂μ) ^ 2 - ‖q‖ ^ 2
  rw [← hPnorm, ← hFnorm, hMean]
  nlinarith

/-- The projected independent-pair energy is exactly twice global Gibbs variance
minus the native one-link conditional-pair energy. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF_eq_two_variance_sub_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF
        target O =
      2 * C.gibbsVarianceBCF O -
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF_eq_two_mul_variance,
    continuous_compact_oriented_singleLinkHeatBathProjectionVarianceBCF_eq_gibbsVariance_sub_fluctuation_norm_sq,
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_two_mul_norm_sq]
  ring

/-- Exact evaluation of the conditional-mean transport square: it is twice the
global Gibbs variance minus the native one-link conditional-pair energy. -/
theorem continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_eq_two_variance_sub_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ z : C.base.Configuration × C.base.Configuration,
      C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
        target O z
      ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      2 * C.gibbsVarianceBCF O -
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  rw [continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_eq_projection_pair_energy,
    continuous_compact_oriented_singleLinkHeatBathProjectionIndependentPairDifferenceEnergyBCF_eq_two_variance_sub_native]

/-- The endpoint cross moment has no remaining conditional-mean term: it is
exactly twice global Gibbs variance minus the single-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_two_variance_sub_single
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O =
      2 * C.gibbsVarianceBCF O -
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_native_sub_single_add_integral_mean_sq,
    continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_eq_two_variance_sub_native]
  ring

/-- Exact sign criterion for the endpoint correlation obstruction.  Cross-moment
nonpositivity is equivalent to the single-trajectory endpoint energy dominating
twice the global Gibbs variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_nonpos_iff_two_variance_le_single
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤ 0 ↔
      2 * C.gibbsVarianceBCF O ≤
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_two_variance_sub_single]
  constructor <;> intro h <;> linarith

/-- Quantitative correlation domination is equivalently a lower bound on the
single-trajectory endpoint energy after adding the allowed native-energy budget. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_le_rho_native_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤
      ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ↔
    2 * C.gibbsVarianceBCF O ≤
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) +
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_two_variance_sub_single]
  constructor <;> intro h <;> linarith

end

end MathlibAnalytic
end MGAP4D
