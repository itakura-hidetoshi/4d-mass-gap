import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryDoubleEndpointEnergyBCF
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Antisymmetric observable on the native independent conditional-pair carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (y : C.base.Configuration × C.base.Configuration) : ℝ :=
  O y.1 - O y.2

/-- The native independent-pair observable is continuous. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous (C.singleLinkHeatBathIndependentPairObservableBCF O) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableBCF
  exact (O.continuous.comp continuous_fst).sub
    (O.continuous.comp continuous_snd)

/-- Squared native conditional-pair observable energy after Gibbs averaging. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ y,
    (C.singleLinkHeatBathIndependentPairObservableBCF O y) ^ 2
    ∂C.singleLinkHeatBathIndependentPairMeasure target

/-- The Gibbs-averaged native conditional-pair observable energy is nonnegative. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The native pair energy is the Gibbs average of the existing fixed-background
conditional independent-pair difference energies. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_integral_fiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O =
      ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure := by
  let f : C.base.Configuration × C.base.Configuration → ℝ := fun y =>
    (C.singleLinkHeatBathIndependentPairObservableBCF O y) ^ 2
  have hfContinuous : Continuous f := by
    dsimp [f]
    exact
      (continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableBCF_continuous
        C O).pow 2
  have hfInt : Integrable f
      (C.singleLinkHeatBathIndependentPairMeasure target) :=
    hfContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfComp : Integrable f
      ((C.singleLinkHeatBathIndependentPairKernel target ∘ₖ
        Kernel.const Unit C.gibbsMeasure) ()) := by
    rw [← Measure.comp_eq_comp_const_apply]
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure]
      using hfInt
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure
  change (∫ y, f y
      ∂(C.singleLinkHeatBathIndependentPairKernel target ∘ₘ C.gibbsMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply]
  calc
    (∫ y, f y
        ∂((C.singleLinkHeatBathIndependentPairKernel target ∘ₖ
          Kernel.const Unit C.gibbsMeasure) ())) =
      ∫ A, ∫ y, f y
        ∂C.singleLinkHeatBathIndependentPairKernel target A
        ∂C.gibbsMeasure := by
      simpa using (ProbabilityTheory.Kernel.integral_comp hfComp)
    _ = ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun A => by
        unfold f
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableBCF
        exact
          continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairKernel_sqDiff
            C target O A

/-- Native pair energy is twice the squared norm of the one-link heat-bath
projection defect. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O =
      2 * ‖C.singleLinkHeatBathFluctuationL2 target
        (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  rw [
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_integral_fiber,
    continuous_compact_oriented_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_norm_sq]

/-- Summing the native pair energies is exactly twice the heat-bath Hamiltonian
quadratic form. -/
theorem continuous_compact_oriented_sum_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_two_mul_hamiltonian
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ target : C.base.geometry.Edge,
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) =
      2 * inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) := by
  calc
    (∑ target : C.base.geometry.Edge,
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) =
      ∑ target : C.base.geometry.Edge,
        ∫ A,
          C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
          ∂C.gibbsMeasure := by
      apply Finset.sum_congr rfl
      intro target _
      exact
        continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_integral_fiber
          C target O
    _ = 2 * inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) :=
      continuous_compact_oriented_sum_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_hamiltonian
        C O

/-- At rank zero, the double-trajectory pair observable square has exactly the
native Gibbs-averaged conditional-pair energy. -/
theorem continuous_compact_oriented_integral_doubleRankPairObservableBCF_zero_sq_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ w,
      (C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
        target O 0 w) ^ 2
      ∂C.independentPairHybridTargetTrajectoryDoubleJointMeasure target) =
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  let pairSq : C.base.Configuration × C.base.Configuration → ℝ := fun y =>
    (C.singleLinkHeatBathIndependentPairObservableBCF O y) ^ 2
  have hRank : Measurable
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
        target 0 (Nat.zero_le _)) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
      C target 0 (Nat.zero_le _)).measurable
  have hPairSq : StronglyMeasurable pairSq := by
    dsimp [pairSq]
    exact
      ((continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableBCF_continuous
        C O).pow 2).stronglyMeasurable
  symm
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
  rw [←
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_zero_eq_native
      C target]
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_eq_map_doubleJoint
      C target 0 (Nat.zero_le _)]
  change (∫ y, pairSq y
      ∂Measure.map
        (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
          target 0 (Nat.zero_le _))
        (C.independentPairHybridTargetTrajectoryDoubleJointMeasure target)) = _
  rw [MeasureTheory.integral_map hRank.aemeasurable
    hPairSq.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp [pairSq]
    rw [
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
        C target O 0 (Nat.zero_le _) w]
    rfl

/-- At the complete canonical rank, the pair observable square again has exactly
the same native conditional-pair energy. -/
theorem continuous_compact_oriented_integral_doubleRankPairObservableBCF_card_sq_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ w,
      (C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
        target O (Fintype.card C.base.geometry.Edge) w) ^ 2
      ∂C.independentPairHybridTargetTrajectoryDoubleJointMeasure target) =
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  let n := Fintype.card C.base.geometry.Edge
  let pairSq : C.base.Configuration × C.base.Configuration → ℝ := fun y =>
    (C.singleLinkHeatBathIndependentPairObservableBCF O y) ^ 2
  have hRank : Measurable
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
        target n le_rfl) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
      C target n le_rfl).measurable
  have hPairSq : StronglyMeasurable pairSq := by
    dsimp [pairSq]
    exact
      ((continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableBCF_continuous
        C O).pow 2).stronglyMeasurable
  symm
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairObservableEnergyBCF
  rw [←
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_card_eq_native
      C target]
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_eq_map_doubleJoint
      C target n le_rfl]
  change (∫ y, pairSq y
      ∂Measure.map
        (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
          target n le_rfl)
        (C.independentPairHybridTargetTrajectoryDoubleJointMeasure target)) = _
  rw [MeasureTheory.integral_map hRank.aemeasurable
    hPairSq.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp [pairSq, n]
    rw [
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
        C target O (Fintype.card C.base.geometry.Edge) le_rfl w]
    rfl

/-- Product of the rank-zero and full-rank pair observables on the common double
trajectory carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) : ℝ :=
  C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF target O 0 w *
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O (Fintype.card C.base.geometry.Edge) w

/-- The endpoint pair-observable cross integrand is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
        target O) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
      C target O 0).mul
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
        C target O (Fintype.card C.base.geometry.Edge))

/-- Endpoint cross moment of the native pair observable along the double
trajectory self-coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ w,
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
      target O w
    ∂C.independentPairHybridTargetTrajectoryDoubleJointMeasure target

/-- The cross integrand is integrable on the double joint probability law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
        target O)
      (C.independentPairHybridTargetTrajectoryDoubleJointMeasure target) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF_continuous
      C target O).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Exact polarization identity: endpoint transport energy is twice the native
pair energy minus twice the endpoint cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_native_sub_two_cross
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O =
      2 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
        2 *
          C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
            target O := by
  let μ := C.independentPairHybridTargetTrajectoryDoubleJointMeasure target
  let d0 : C.independentPairHybridTargetTrajectoryDoubleJointCarrier → ℝ := fun w =>
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O 0 w
  let dn : C.independentPairHybridTargetTrajectoryDoubleJointCarrier → ℝ := fun w =>
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O (Fintype.card C.base.geometry.Edge) w
  have h0 : Integrable (fun w => (d0 w) ^ 2) μ := by
    exact
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
        C target O 0).pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hn : Integrable (fun w => (dn w) ^ 2) μ := by
    exact
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
        C target O (Fintype.card C.base.geometry.Edge)).pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hcross : Integrable (fun w => d0 w * dn w) μ := by
    exact
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
        C target O 0).mul
        (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
          C target O (Fintype.card C.base.geometry.Edge))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
  change (∫ w, (d0 w - dn w) ^ 2 ∂μ) = _
  calc
    (∫ w, (d0 w - dn w) ^ 2 ∂μ) =
      ∫ w, ((d0 w) ^ 2 + (dn w) ^ 2 - 2 * (d0 w * dn w)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => by ring
    _ = (∫ w, ((d0 w) ^ 2 + (dn w) ^ 2) ∂μ) -
        ∫ w, 2 * (d0 w * dn w) ∂μ := by
      exact integral_sub (h0.add hn) (hcross.const_mul 2)
    _ = ((∫ w, (d0 w) ^ 2 ∂μ) +
        ∫ w, (dn w) ^ 2 ∂μ) -
          ∫ w, 2 * (d0 w * dn w) ∂μ := by
      rw [integral_add h0 hn]
    _ = (∫ w, (d0 w) ^ 2 ∂μ) +
        (∫ w, (dn w) ^ 2 ∂μ) -
          2 * (∫ w, d0 w * dn w ∂μ) := by
      rw [integral_const_mul]
    _ = 2 * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
        2 *
          C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
            target O := by
      rw [
        continuous_compact_oriented_integral_doubleRankPairObservableBCF_zero_sq_eq_native,
        continuous_compact_oriented_integral_doubleRankPairObservableBCF_card_sq_eq_native]
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
      change
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O +
            C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
          2 * (∫ w, d0 w * dn w ∂μ) = _
      ring

/-- A quantitative upper bound on the endpoint cross moment recovers a matching
lower bound for the endpoint transport energy. -/
theorem continuous_compact_oriented_two_mul_one_sub_mul_nativePairEnergy_le_doubleEndpointEnergy_of_cross_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ)
    (hCross :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    2 * (1 - ρ) *
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ≤
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O := by
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_native_sub_two_cross]
  nlinarith

/-- Combining endpoint correlation domination with the completed source-path
transport bound yields a conditional native-pair profile estimate. -/
theorem continuous_compact_oriented_two_mul_one_sub_mul_nativePairEnergy_le_boundaryResidualPath_add_variation_of_cross_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (ρ : ℝ)
    (hCross :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    2 * (1 - ρ) *
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ≤
      4 *
        ((Fintype.card C.base.geometry.Edge : ℝ) *
          (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
            2 * ∑ source : C.base.geometry.Edge,
              (P.variation source) ^ 2)) := by
  exact le_trans
    (continuous_compact_oriented_two_mul_one_sub_mul_nativePairEnergy_le_doubleEndpointEnergy_of_cross_le
      C target O ρ hCross)
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_boundaryResidualPath_add_variation
      C target O P)

/-- If the endpoint pair-observable cross moment is nonpositive, the one-link
heat-bath fluctuation norm is controlled directly by the established source-path
and variation budget. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_norm_sq_le_boundaryResidualPath_add_variation_of_cross_nonpos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (hCross :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤ 0) :
    ‖C.singleLinkHeatBathFluctuationL2 target
        (C.gibbsL2RepresentativeBCF O)‖ ^ 2 ≤
      (Fintype.card C.base.geometry.Edge : ℝ) *
        (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
          2 * ∑ source : C.base.geometry.Edge,
            (P.variation source) ^ 2) := by
  have hCrossZero :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        (0 : ℝ) *
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
    simpa using hCross
  have hBound :=
    continuous_compact_oriented_two_mul_one_sub_mul_nativePairEnergy_le_boundaryResidualPath_add_variation_of_cross_le
      C target O P 0 hCrossZero
  rw [
    continuous_compact_oriented_singleLinkHeatBathIndependentPairObservableEnergyBCF_eq_two_mul_norm_sq]
    at hBound
  nlinarith

/-- Under nonpositive endpoint cross moments for every target link, the full
heat-bath Hamiltonian quadratic form is bounded by the sum of the established
source-path and variation budgets. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm_le_sum_boundaryResidualPath_add_variation_of_cross_nonpos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (hCross : ∀ target : C.base.geometry.Edge,
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤ 0) :
    inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) ≤
      ∑ target : C.base.geometry.Edge,
        (Fintype.card C.base.geometry.Edge : ℝ) *
          (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
            2 * ∑ source : C.base.geometry.Edge,
              (P.variation source) ^ 2) := by
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
  apply Finset.sum_le_sum
  intro target _
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_norm_sq_le_boundaryResidualPath_add_variation_of_cross_nonpos
      C target O P (hCross target)

end

end MathlibAnalytic
end MGAP4D
