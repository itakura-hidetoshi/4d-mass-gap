import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointLinkLocalEnergy

/-!
# Exact posterior resampling Dirichlet energies of signed transfer inputs

The original one-link conditional projection is stationary under the ORIGINAL
joint law. Its squared residual is exactly ONE HALF the joint/posterior average
of the squared two-point difference. This is an equality, not a Jensen bound.

For the actual transfer observable, that difference is the SIGNED source
integral constructed in #5222. Both levels of integrability are proved. The
normalized link sum is therefore (1/12) times the sum of resampling energies.
The existing endpoint-dependent envelope now gives half the former one-link
bound, and halves the near-set coefficient while retaining exact exterior
energy. There is still an explicit link count in the uniform specialization.

No spatial-decay or volume-uniform theorem is asserted. No source cancellation,
physicality, projection/transfer commutation or excited-sector property of the
absolute input is assumed. The frozen orbit remains at beta(n+1), with the last
transfer and original joint half-density at beta(n), including r=0.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStatePosteriorJoint

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "Mean" => posteriorMean H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Local" => jointTransferLocalEnergyOn H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "Rate" => kernelRightVariationRate beta

local instance resamplingJointProbability : IsProbabilityMeasure μJ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

local instance resamplingFiberProbability (z : Joint) (e : Link) :
    IsProbabilityMeasure (Nu z.1 z.2 e) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
    H N hN beta hbeta z.1 z.2 e

/-- Stationarity of the literal posterior integral on the original bounded core. -/
theorem posteriorMean_integral_eq (e : Link) (F : Joint → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫ z, Mean e F z ∂μJ) = ∫ z, F z ∂μJ := by
  let f : JL2 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta F hF bound hbound
  have hf : (fun z => f z) =ᵐ[μJ] F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta F hF bound hbound
  have hp : (fun z => PJoint e f z) =ᵐ[μJ] Mean e F :=
    condExpL2_coeFn_eq_posteriorMean H N hN beta hbeta e F hF bound hbound
  have hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le H N e
  calc
    _ = ∫ z, PJoint e f z ∂μJ := integral_congr_ae hp.symm
    _ = ∫ z, f z ∂μJ := by
      simpa only [Measure.restrict_univ] using
        (integral_condExpL2_eq_of_fin_meas_real (𝕜 := ℝ) (hm := hm)
          f (s := Set.univ) MeasurableSet.univ (measure_ne_top _ _))
    _ = _ := integral_congr_ae hf

private theorem resamplingFiber_continuous (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    Continuous (fun g : GaugeT => F (z.1, Function.update z.2 e g)) := by
  classical
  have hu : Continuous (fun g : GaugeT => Function.update z.2 e g) := by
    apply continuous_pi
    intro j
    by_cases hj : j = e
    · subst j
      simpa only [Function.update_self] using (continuous_id : Continuous (fun g : GaugeT => g))
    · simpa only [Function.update_of_ne hj] using
        (continuous_const : Continuous (fun _ : GaugeT => z.2 j))
  exact F.continuous.comp (continuous_const.prodMk hu)

private theorem resamplingFiber_integrable (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    Integrable (fun g : GaugeT => F (z.1, Function.update z.2 e g)) (Nu z.1 z.2 e) := by
  apply (integrable_const ‖F‖).mono'
    (resamplingFiber_continuous H N e F z).aestronglyMeasurable
  exact Eventually.of_forall fun g => F.norm_coe_le_norm _

private theorem resamplingFiber_square_integrable (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    Integrable (fun g : GaugeT => F (z.1, Function.update z.2 e g) ^ 2) (Nu z.1 z.2 e) := by
  have hf : MemLp (fun g : GaugeT => F (z.1, Function.update z.2 e g)) 2 (Nu z.1 z.2 e) :=
    MemLp.of_bound (resamplingFiber_continuous H N e F z).aestronglyMeasurable
      ‖F‖ (Eventually.of_forall fun g => F.norm_coe_le_norm _)
  exact hf.integrable_sq

private theorem resamplingSquare_norm_le (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    ‖F z ^ 2‖ ≤ ‖F‖ ^ 2 := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (F.norm_coe_le_norm z) 2

/-- The inner squared difference is integrable in the actual posterior fiber. -/
theorem posteriorResamplingDifferenceSquare_integrable (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    Integrable (fun g : GaugeT => (F z - F (z.1, Function.update z.2 e g)) ^ 2)
      (Nu z.1 z.2 e) := by
  have hf := resamplingFiber_integrable H N hN beta hbeta e F z
  have hf2 := resamplingFiber_square_integrable H N hN beta hbeta e F z
  apply (((integrable_const (F z ^ 2)).sub (hf.const_mul (2 * F z))).add hf2).congr
  exact Eventually.of_forall fun g => by
    change F z ^ 2 - (2 * F z) * F (z.1, Function.update z.2 e g) +
      F (z.1, Function.update z.2 e g) ^ 2 = _
    ring

/-- Mean square of the original two-point difference, before joint averaging. -/
def posteriorResamplingSquare (e : Link) (F : BoundedContinuousFunction Joint ℝ) (z : Joint) : ℝ :=
  ∫ g, (F z - F (z.1, Function.update z.2 e g)) ^ 2 ∂Nu z.1 z.2 e

theorem posteriorResamplingSquare_nonneg (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    0 ≤ posteriorResamplingSquare H N hN beta hbeta e F z :=
  integral_nonneg fun _ => sq_nonneg _

/-- Pointwise expansion into residual square and conditional variance terms. -/
theorem posteriorResamplingSquare_formula (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    posteriorResamplingSquare H N hN beta hbeta e F z =
      (F z - Mean e F z) ^ 2 + Mean e (fun w => F w ^ 2) z - (Mean e F z) ^ 2 := by
  have hf := resamplingFiber_integrable H N hN beta hbeta e F z
  have hf2 := resamplingFiber_square_integrable H N hN beta hbeta e F z
  have hc : (∫ _g : GaugeT, F z ^ 2 ∂Nu z.1 z.2 e) = F z ^ 2 := by simp
  calc
    _ = ∫ g, (F z ^ 2 - (2 * F z) * F (z.1, Function.update z.2 e g)) +
        F (z.1, Function.update z.2 e g) ^ 2 ∂Nu z.1 z.2 e :=
      integral_congr_ae (Eventually.of_forall fun _ => by ring)
    _ = F z ^ 2 - (2 * F z) * Mean e F z + Mean e (fun w => F w ^ 2) z := by
      change _ = F z ^ 2 - (2 * F z) *
        (∫ g, F (z.1, Function.update z.2 e g) ∂Nu z.1 z.2 e) +
        ∫ g, F (z.1, Function.update z.2 e g) ^ 2 ∂Nu z.1 z.2 e
      rw [integral_add ((integrable_const (F z ^ 2)).sub (hf.const_mul (2 * F z))) hf2,
        integral_sub (integrable_const (F z ^ 2)) (hf.const_mul (2 * F z)),
        integral_const_mul, hc]
    _ = _ := by ring

/-- The outer resampling square is integrable, not merely a totalized integral. -/
theorem posteriorResamplingSquare_integrable (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) :
    Integrable (posteriorResamplingSquare H N hN beta hbeta e F) μJ := by
  have hr := posteriorStageResidual_sq_integrable H N hN beta hbeta [] e F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  change Integrable (fun z => (F z - Mean e F z) ^ 2) μJ at hr
  have hm := (posteriorMean_memLp_two H N hN beta hbeta e F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm).integrable_sq
  have hq := (posteriorMean_memLp_two H N hN beta hbeta e (fun w => F w ^ 2)
    (F.continuous.pow 2).stronglyMeasurable (‖F‖ ^ 2)
    (resamplingSquare_norm_le H N F)).integrable (by norm_num)
  exact ((hr.add hq).sub hm).congr (Eventually.of_forall fun z =>
    (posteriorResamplingSquare_formula H N hN beta hbeta e F z).symm)

/-- Double integral under the original joint law and original posterior fibers. -/
def posteriorResamplingEnergy (e : Link) (F : BoundedContinuousFunction Joint ℝ) : ℝ :=
  ∫ z, posteriorResamplingSquare H N hN beta hbeta e F z ∂μJ

private theorem resampling_norm_sq_of_ae (f : JL2) (G : Joint → ℝ)
    (h : (fun z => f z) =ᵐ[μJ] G) : ‖f‖ ^ 2 = ∫ z, G z ^ 2 ∂μJ := by
  rw [realL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Exact Dirichlet identity. The factor two comes from stationarity and
orthogonal projection; no Jensen inequality or independent joint law is used. -/
theorem posteriorResamplingEnergy_eq_twice_stageEnergy (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) :
    posteriorResamplingEnergy H N hN beta hbeta e F =
      2 * posteriorStageResidualEnergy H N hN beta hbeta [] e F := by
  let f := posteriorScheduleL2 H N hN beta hbeta [] F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  let p := posteriorScheduleL2 H N hN beta hbeta ([] ++ [e]) F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  have hf : (fun z => f z) =ᵐ[μJ] (fun z => F z) :=
    (posteriorSchedule_memLp_two H N hN beta hbeta [] F
      F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm).coeFn_toLp
  have hp : (fun z => p z) =ᵐ[μJ] Mean e F :=
    (posteriorSchedule_memLp_two H N hN beta hbeta ([] ++ [e]) F
      F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm).coeFn_toLp
  have hLoss := posteriorStageResidualEnergy_eq_norm_loss H N hN beta hbeta [] e F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  change posteriorStageResidualEnergy H N hN beta hbeta [] e F = ‖f‖ ^ 2 - ‖p‖ ^ 2 at hLoss
  rw [resampling_norm_sq_of_ae H N hN beta hbeta f F hf,
    resampling_norm_sq_of_ae H N hN beta hbeta p (Mean e F) hp] at hLoss
  have hr := posteriorStageResidual_sq_integrable H N hN beta hbeta [] e F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  change Integrable (fun z => (F z - Mean e F z) ^ 2) μJ at hr
  have hm := (posteriorMean_memLp_two H N hN beta hbeta e F
    F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm).integrable_sq
  have hq := (posteriorMean_memLp_two H N hN beta hbeta e (fun w => F w ^ 2)
    (F.continuous.pow 2).stronglyMeasurable (‖F‖ ^ 2)
    (resamplingSquare_norm_le H N F)).integrable (by norm_num)
  have hStationary := posteriorMean_integral_eq H N hN beta hbeta e (fun w => F w ^ 2)
    (F.continuous.pow 2).stronglyMeasurable (‖F‖ ^ 2) (resamplingSquare_norm_le H N F)
  calc
    _ = ∫ z, ((F z - Mean e F z) ^ 2 + Mean e (fun w => F w ^ 2) z) -
        (Mean e F z) ^ 2 ∂μJ :=
      integral_congr_ae (Eventually.of_forall (posteriorResamplingSquare_formula H N hN beta hbeta e F))
    _ = posteriorStageResidualEnergy H N hN beta hbeta [] e F +
        (∫ z, F z ^ 2 ∂μJ) - ∫ z, (Mean e F z) ^ 2 ∂μJ := by
      change _ = (∫ z, (F z - Mean e F z) ^ 2 ∂μJ) +
        (∫ z, F z ^ 2 ∂μJ) - ∫ z, (Mean e F z) ^ 2 ∂μJ
      rw [integral_sub (hr.add hq) hm, integral_add hr hq, hStationary]
    _ = _ := by linarith

/-- Exact half-resampling formula for the existing genuine joint projection. -/
theorem posteriorInitialResidual_sq_eq_half_resampling (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) :
    ‖BCFRep F - PJoint e (BCFRep F)‖ ^ 2 =
      (1 / 2 : ℝ) * posteriorResamplingEnergy H N hN beta hbeta e F := by
  have h := posteriorResamplingEnergy_eq_twice_stageEnergy H N hN beta hbeta e F
  rw [posteriorStageEnergy_eq_bcfResidualNormSq] at h
  simp only [realHilbertProjectionSweep, ContinuousLinearMap.id_apply] at h
  linarith

/-- Source integration remains SIGNED and is completed before squaring. -/
def jointTransferLinkResamplingEnergy (x : PairL2) (e : Link) : ℝ :=
  ∫ z, (∫ g, jointTransferLinkDifference H N hN beta hbeta x e z g ^ 2
    ∂Nu z.1 z.2 e) ∂μJ

theorem jointTransferLinkDifference_sq_posterior_integrable (x : PairL2) (e : Link) (z : Joint) :
    Integrable (fun g => jointTransferLinkDifference H N hN beta hbeta x e z g ^ 2)
      (Nu z.1 z.2 e) := by
  simpa only [jointTransferLinkDifference_eq] using
    posteriorResamplingDifferenceSquare_integrable H N hN beta hbeta e (Obs x) z

theorem jointTransferLinkResamplingSquare_integrable (x : PairL2) (e : Link) :
    Integrable (fun z => ∫ g, jointTransferLinkDifference H N hN beta hbeta x e z g ^ 2
      ∂Nu z.1 z.2 e) μJ := by
  simpa only [jointTransferLinkDifference_eq, posteriorResamplingSquare] using
    posteriorResamplingSquare_integrable H N hN beta hbeta e (Obs x)

theorem jointTransferLinkResamplingEnergy_eq (x : PairL2) (e : Link) :
    jointTransferLinkResamplingEnergy H N hN beta hbeta x e =
      posteriorResamplingEnergy H N hN beta hbeta e (Obs x) := by
  unfold jointTransferLinkResamplingEnergy posteriorResamplingEnergy posteriorResamplingSquare
  simp only [jointTransferLinkDifference_eq]

/-- #5222's actual initial link energy is exactly half the signed resampling energy. -/
theorem jointTransferLinkResamplingEnergy_eq_twice_localEnergy (x : PairL2) (e : Link) :
    jointTransferLinkResamplingEnergy H N hN beta hbeta x e =
      2 * jointTransferLinkLocalEnergy H N hN beta hbeta x e := by
  rw [jointTransferLinkResamplingEnergy_eq, posteriorResamplingEnergy_eq_twice_stageEnergy]
  congr 1
  unfold posteriorStageResidualEnergy jointTransferLinkLocalEnergy
  apply integral_congr_ae
  filter_upwards with z
  rw [jointTransferSignedLinkResidual_eq_stage]

/-- The normalization is 1/12, with the existing link set and no count inflation. -/
theorem jointTransferLocalEnergyOn_eq_resampling (x : PairL2) (s : Finset Link) :
    Local x s = (1 / 12 : ℝ) *
      ∑ e ∈ s, jointTransferLinkResamplingEnergy H N hN beta hbeta x e := by
  unfold jointTransferLocalEnergyOn
  simp_rw [jointTransferLinkResamplingEnergy_eq_twice_localEnergy]
  rw [← Finset.mul_sum]
  ring

/-- A genuine quantitative improvement: half of the former one-link envelope. -/
theorem jointTransferLinkLocalEnergy_le_half_l2Envelope (x : PairL2) (e : Link) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e ≤
      (1 / 2 : ℝ) * (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  let F := Obs x
  let W := jointTransferEnvelope H N hN beta hbeta x
  have hPoint : ∀ z, posteriorResamplingSquare H N hN beta hbeta e F z ≤ (Rate * W z) ^ 2 := by
    intro z
    calc
      _ ≤ ∫ _g : GaugeT, (Rate * W z) ^ 2 ∂Nu z.1 z.2 e := by
        apply integral_mono (posteriorResamplingDifferenceSquare_integrable H N hN beta hbeta e F z)
          (integrable_const _)
        intro g
        have hAbs : |F z - F (z.1, Function.update z.2 e g)| ≤ Rate * W z := by
          apply jointTransferBCF_right_variation H N hN beta hbeta x z.1 e z.2
          intro j hj
          rw [Function.update_of_ne hj]
        have hSq := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
        simpa only [sq_abs] using hSq
      _ = _ := by simp
  have hWlp : MemLp (fun z => W z) 2 μJ :=
    MemLp.of_bound W.continuous.aestronglyMeasurable ‖W‖ (Eventually.of_forall W.norm_coe_le_norm)
  have hI := integral_mono (posteriorResamplingSquare_integrable H N hN beta hbeta e F)
    (hWlp.const_mul Rate).integrable_sq hPoint
  have hWrep : (∫ z, W z ^ 2 ∂μJ) = ‖BCFRep W‖ ^ 2 := by
    rw [realL2_norm_sq_eq_integral_norm_sq (BCFRep W)]
    apply integral_congr_ae
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μJ ℝ W] with z hz
    change W z ^ 2 = ‖(BoundedContinuousFunction.toLp 2 μJ ℝ W) z‖ ^ 2
    rw [hz]
    simp only [Real.norm_eq_abs, sq_abs]
  have hScale : (∫ z, (Rate * W z) ^ 2 ∂μJ) =
      Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul, hWrep]
    rw [jointTransferEnvelope_rep_norm]
  have hExact := jointTransferLinkResamplingEnergy_eq_twice_localEnergy H N hN beta hbeta x e
  rw [jointTransferLinkResamplingEnergy_eq] at hExact
  change posteriorResamplingEnergy H N hN beta hbeta e F =
    2 * jointTransferLinkLocalEnergy H N hN beta hbeta x e at hExact
  change posteriorResamplingEnergy H N hN beta hbeta e F ≤ _ at hI
  rw [hScale] at hI
  linarith

/-- Apply the sharper bound only inside the chosen link set. -/
theorem jointTransferLocalEnergyOn_le_card_half_l2Envelope (x : PairL2) (s : Finset Link) :
    Local x s ≤ (1 / 12 : ℝ) * (s.card : ℝ) *
      (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  have hSum := Finset.sum_le_sum (s := s) fun e _ =>
    jointTransferLinkLocalEnergy_le_half_l2Envelope H N hN beta hbeta x e
  unfold jointTransferLocalEnergyOn
  calc
    _ ≤ (1 / 6 : ℝ) * ∑ _e ∈ s,
        (1 / 2 : ℝ) * (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Near coefficient 1/3 instead of 2/3; exterior is still the exact energy. -/
theorem jointTransferProfileEnergy_le_half_localEnvelope_add_exterior (x : PairL2) (s : Finset Link) :
    Profile (BCFRep (Obs x)) ≤ (1 / 3 : ℝ) * (s.card : ℝ) *
      (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) + 4 * Local x sᶜ := by
  have hp := sixColorProfileEnergy_le_four_initialResidualEnergy H N hN beta hbeta (BCFRep (Obs x))
  have hs := jointTransferLocalEnergyOn_add_compl H N hN beta hbeta x s
  have hl := jointTransferLocalEnergyOn_le_card_half_l2Envelope H N hN beta hbeta x s
  nlinarith

/-- Uniform specialization retains the explicit number of actual spatial links. -/
theorem jointTransferProfileEnergy_le_half_l2Envelope (x : PairL2) :
    Profile (BCFRep (Obs x)) ≤ (1 / 3 : ℝ) * (Fintype.card Link : ℝ) *
      (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  simpa [jointTransferLocalEnergyOn] using
    jointTransferProfileEnergy_le_half_localEnvelope_add_exterior H N hN beta hbeta x Finset.univ

end GeneralCarrier

section FrozenFamily

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenVec" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenEnergy" => physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
  Hn 2 Pos (beta n) (hbeta n)

/-- Exact resampling formula for the unchanged actual frozen family, including r=0. -/
theorem fineFrozenInitialEnergy_eq_resampling :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n) FrozenVec =
      (1 / 12 : ℝ) * ∑ e : Link,
        jointTransferLinkResamplingEnergy Hn 2 Pos (beta n) (hbeta n) Orbit e := by
  rw [fineFrozenInitialEnergy_eq_linkLocal, jointTransferLocalEnergyOn_eq_resampling]

/-- Sharpened actual-frozen bound with the exact exterior contribution retained. -/
theorem fineFrozenProfileEnergy_le_half_localEnvelope_add_exterior (s : Finset Link) :
    FrozenEnergy ≤ (1 / 3 : ℝ) * (s.card : ℝ) *
      ((kernelRightVariationRate (beta n)) ^ 2 * ‖NormTransfer (pairAbsoluteInput Hn 2 Orbit)‖ ^ 2) +
      4 * jointTransferLocalEnergyOn Hn 2 Pos (beta n) (hbeta n) Orbit sᶜ := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  rw [← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  simpa only [fineFrozenBCF] using
    jointTransferProfileEnergy_le_half_localEnvelope_add_exterior Hn 2 Pos (beta n) (hbeta n) Orbit s

/-- No excited-sector contraction is applied to the absolute orbit input. -/
theorem fineFrozenProfileEnergy_le_half_l2Envelope :
    FrozenEnergy ≤ (1 / 3 : ℝ) * (Fintype.card Link : ℝ) *
      ((kernelRightVariationRate (beta n)) ^ 2 * ‖NormTransfer (pairAbsoluteInput Hn 2 Orbit)‖ ^ 2) := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  rw [← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  simpa only [fineFrozenBCF] using
    jointTransferProfileEnergy_le_half_l2Envelope Hn 2 Pos (beta n) (hbeta n) Orbit

end FrozenFamily

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
