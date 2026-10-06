import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSweepL2Envelope

/-!
# Signed link-local energy on the original posterior joint carrier

Keep the source kernel difference signed until AFTER both the source and
posterior integrals. Its square integral is exactly the existing initial
one-link L2 defect, not an assumed bound or a replacement observable.

Finite-link energies retain the six-color normalization 1/6. Their exact
set/complement splitting gives a near-link envelope plus an UNCHANGED exterior
energy. A kernel-cancellation criterion is conditional: it is not asserted for
the actual frozen family. No spatial tail, volume-uniform estimate, response
matrix, Dobrushin cutoff, or physicality statement is supplied here.
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
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "J" => jointTransferKernel H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "Rate" => kernelRightVariationRate beta

/-- Signed source integral for a specific right-link replacement. -/
def jointTransferLinkDifference (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) : ℝ :=
  ∫ y, (J y z - J y (z.1, Function.update z.2 e g)) * x y ∂μP

theorem jointTransferLinkDifference_integrable (x : PairL2) (e : Link)
    (z : Joint) (g : GaugeT) :
    Integrable (fun y => (J y z - J y (z.1, Function.update z.2 e g)) * x y) μP := by
  have h := (jointTransferKernel_integrable H N hN beta hbeta x z).sub
    (jointTransferKernel_integrable H N hN beta hbeta x (z.1, Function.update z.2 e g))
  convert h using 1
  funext y
  exact sub_mul _ _ _

/-- The source integral preserves the exact sign and cancellation of the BCF difference. -/
theorem jointTransferLinkDifference_eq (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    jointTransferLinkDifference H N hN beta hbeta x e z g =
      Obs x z - Obs x (z.1, Function.update z.2 e g) := by
  unfold jointTransferLinkDifference
  rw [jointTransferBCF_eq_integral_kernel, jointTransferBCF_eq_integral_kernel,
    ← integral_sub (jointTransferKernel_integrable H N hN beta hbeta x z)
      (jointTransferKernel_integrable H N hN beta hbeta x (z.1, Function.update z.2 e g))]
  exact integral_congr_ae (Eventually.of_forall fun y => sub_mul _ _ _)

private theorem linkLocalFiber_continuous (x : PairL2) (e : Link) (z : Joint) :
    Continuous (fun g : GaugeT => Obs x (z.1, Function.update z.2 e g)) := by
  classical
  have hUpdate : Continuous (fun g : GaugeT => Function.update z.2 e g) := by
    apply continuous_pi
    intro j
    by_cases hj : j = e
    · subst j
      simpa only [Function.update_self] using (continuous_id : Continuous (fun g : GaugeT => g))
    · simpa only [Function.update_of_ne hj] using
        (continuous_const : Continuous (fun _ : GaugeT => z.2 j))
  exact (Obs x).continuous.comp (continuous_const.prodMk hUpdate)

private theorem linkLocalFiber_integrable (x : PairL2) (e : Link) (z : Joint) :
    Integrable (fun g : GaugeT => Obs x (z.1, Function.update z.2 e g)) (Nu z.1 z.2 e) := by
  letI : IsProbabilityMeasure (Nu z.1 z.2 e) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta z.1 z.2 e
  apply (integrable_const ‖Obs x‖).mono'
    (linkLocalFiber_continuous H N hN beta hbeta x e z).aestronglyMeasurable
  exact Eventually.of_forall fun g => (Obs x).norm_coe_le_norm (z.1, Function.update z.2 e g)

/-- The second integral is also genuine, for the existing posterior fiber law. -/
theorem jointTransferLinkDifference_posterior_integrable (x : PairL2) (e : Link) (z : Joint) :
    Integrable (jointTransferLinkDifference H N hN beta hbeta x e z) (Nu z.1 z.2 e) := by
  letI : IsProbabilityMeasure (Nu z.1 z.2 e) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta z.1 z.2 e
  have hfun : jointTransferLinkDifference H N hN beta hbeta x e z =
      fun g => Obs x z - Obs x (z.1, Function.update z.2 e g) :=
    funext (jointTransferLinkDifference_eq H N hN beta hbeta x e z)
  rw [hfun]
  exact (integrable_const (Obs x z)).sub (linkLocalFiber_integrable H N hN beta hbeta x e z)

/-- Posterior average of the SIGNED source integral; no absolute input occurs. -/
def jointTransferSignedLinkResidual (x : PairL2) (e : Link) (z : Joint) : ℝ :=
  ∫ g, jointTransferLinkDifference H N hN beta hbeta x e z g ∂Nu z.1 z.2 e

theorem jointTransferSignedLinkResidual_eq (x : PairL2) (e : Link) (z : Joint) :
    jointTransferSignedLinkResidual H N hN beta hbeta x e z =
      Obs x z - posteriorMean H N hN beta hbeta e (Obs x) z := by
  letI : IsProbabilityMeasure (Nu z.1 z.2 e) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta z.1 z.2 e
  unfold jointTransferSignedLinkResidual
  simp only [jointTransferLinkDifference_eq]
  rw [integral_sub (integrable_const (Obs x z)) (linkLocalFiber_integrable H N hN beta hbeta x e z)]
  have hConst : (∫ _g : GaugeT, Obs x z ∂Nu z.1 z.2 e) = Obs x z := by simp
  simp only [hConst, posteriorMean]

/-- Reuse the already identified empty-prefix residual, not a new L2 carrier. -/
theorem jointTransferSignedLinkResidual_eq_stage (x : PairL2) (e : Link) (z : Joint) :
    jointTransferSignedLinkResidual H N hN beta hbeta x e z =
      posteriorStageResidual H N hN beta hbeta [] e (Obs x) z :=
  jointTransferSignedLinkResidual_eq H N hN beta hbeta x e z

theorem jointTransferSignedLinkResidual_memLp_two (x : PairL2) (e : Link) :
    MemLp (jointTransferSignedLinkResidual H N hN beta hbeta x e) 2 μJ := by
  have hfun : jointTransferSignedLinkResidual H N hN beta hbeta x e =
      posteriorStageResidual H N hN beta hbeta [] e (Obs x) :=
    funext (jointTransferSignedLinkResidual_eq_stage H N hN beta hbeta x e)
  rw [hfun]
  exact posteriorStageResidual_memLp_two H N hN beta hbeta [] e (Obs x)
    (Obs x).continuous.stronglyMeasurable ‖Obs x‖ (Obs x).norm_coe_le_norm

theorem jointTransferSignedLinkResidual_sq_integrable (x : PairL2) (e : Link) :
    Integrable (fun z => (jointTransferSignedLinkResidual H N hN beta hbeta x e z) ^ 2) μJ :=
  (jointTransferSignedLinkResidual_memLp_two H N hN beta hbeta x e).integrable_sq

/-- Link-resolved genuine joint square integral, after both signed integrations. -/
def jointTransferLinkLocalEnergy (x : PairL2) (e : Link) : ℝ :=
  ∫ z, (jointTransferSignedLinkResidual H N hN beta hbeta x e z) ^ 2 ∂μJ

theorem jointTransferLinkLocalEnergy_eq_initialResidual_sq (x : PairL2) (e : Link) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e =
      ‖BCFRep (Obs x) - PJoint e (BCFRep (Obs x))‖ ^ 2 := by
  have hEnergy : jointTransferLinkLocalEnergy H N hN beta hbeta x e =
      posteriorStageResidualEnergy H N hN beta hbeta [] e (Obs x) := by
    unfold jointTransferLinkLocalEnergy posteriorStageResidualEnergy
    simp only [jointTransferSignedLinkResidual_eq_stage]
  rw [hEnergy]
  simpa only [realHilbertProjectionSweep, ContinuousLinearMap.id_apply] using
    posteriorStageEnergy_eq_bcfResidualNormSq H N hN beta hbeta [] e (Obs x)

theorem jointTransferLinkLocalEnergy_nonneg (x : PairL2) (e : Link) :
    0 ≤ jointTransferLinkLocalEnergy H N hN beta hbeta x e := by
  rw [jointTransferLinkLocalEnergy_eq_initialResidual_sq]
  exact sq_nonneg _

/-- A source-level cancellation criterion; no such cancellation is assumed of the model. -/
theorem jointTransferLinkLocalEnergy_eq_zero_of_ae_kernelCancellation (x : PairL2) (e : Link)
    (hcancel : ∀ᵐ z ∂μJ, ∀ᵐ g ∂Nu z.1 z.2 e,
      jointTransferLinkDifference H N hN beta hbeta x e z g = 0) :
    jointTransferLinkLocalEnergy H N hN beta hbeta x e = 0 := by
  have hResidual : jointTransferSignedLinkResidual H N hN beta hbeta x e =ᵐ[μJ] 0 := by
    filter_upwards [hcancel] with z hz
    change (∫ g, jointTransferLinkDifference H N hN beta hbeta x e z g ∂Nu z.1 z.2 e) = 0
    calc
      _ = ∫ _g : GaugeT, (0 : ℝ) ∂Nu z.1 z.2 e := integral_congr_ae hz
      _ = 0 := by simp
  unfold jointTransferLinkLocalEnergy
  calc
    _ = ∫ _z : Joint, (0 : ℝ) ∂μJ := by
      apply integral_congr_ae
      filter_upwards [hResidual] with z hz
      simp only [Pi.zero_apply] at hz
      simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    _ = 0 := by simp

/-- Finite-link energy with the ORIGINAL six-color normalization. -/
def jointTransferLocalEnergyOn (x : PairL2) (s : Finset Link) : ℝ :=
  (1 / 6 : ℝ) * ∑ e ∈ s, jointTransferLinkLocalEnergy H N hN beta hbeta x e

local notation "Local" => jointTransferLocalEnergyOn H N hN beta hbeta

theorem jointTransferLocalEnergyOn_empty (x : PairL2) : Local x ∅ = 0 := by
  simp [jointTransferLocalEnergyOn]

theorem jointTransferLocalEnergyOn_nonneg (x : PairL2) (s : Finset Link) : 0 ≤ Local x s :=
  mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun e _ => jointTransferLinkLocalEnergy_nonneg H N hN beta hbeta x e)

theorem jointTransferLocalEnergyOn_univ_eq_initial (x : PairL2) :
    Local x Finset.univ = sixColorInitialResidualEnergy H N hN beta hbeta (BCFRep (Obs x)) := by
  unfold jointTransferLocalEnergyOn sixColorInitialResidualEnergy
  simp only [jointTransferLinkLocalEnergy_eq_initialResidual_sq]

/-- Exact near/exterior splitting. There is no cardinality estimate on the exterior. -/
theorem jointTransferLocalEnergyOn_add_compl (x : PairL2) (s : Finset Link) :
    Local x s + Local x sᶜ = sixColorInitialResidualEnergy H N hN beta hbeta (BCFRep (Obs x)) := by
  rw [← jointTransferLocalEnergyOn_univ_eq_initial]
  unfold jointTransferLocalEnergyOn
  rw [← mul_add, Finset.sum_add_sum_compl]

theorem jointTransferLocalEnergyOn_mono (x : PairL2) {s t : Finset Link} (hst : s ⊆ t) :
    Local x s ≤ Local x t := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 6)
  exact Finset.sum_le_sum_of_subset_of_nonneg hst
    (fun e _ _ => jointTransferLinkLocalEnergy_nonneg H N hN beta hbeta x e)

/-- Only the selected links are replaced by the old constructed L2 envelope. -/
theorem jointTransferLocalEnergyOn_le_card_l2Envelope (x : PairL2) (s : Finset Link) :
    Local x s ≤ (1 / 6 : ℝ) * (s.card : ℝ) *
      (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  have hSum : (∑ e ∈ s, jointTransferLinkLocalEnergy H N hN beta hbeta x e) ≤
      ∑ _e ∈ s, Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro e _
    rw [jointTransferLinkLocalEnergy_eq_initialResidual_sq]
    exact jointTransferInitialResidual_sq_le_l2Envelope H N hN beta hbeta x e
  calc
    _ ≤ (1 / 6 : ℝ) * ∑ _e ∈ s, Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Six-color bound with the exact exterior energy preserved instead of #Link. -/
theorem jointTransferProfileEnergy_le_localEnvelope_add_exterior (x : PairL2) (s : Finset Link) :
    Profile (BCFRep (Obs x)) ≤
      (2 / 3 : ℝ) * (s.card : ℝ) *
        (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) + 4 * Local x sᶜ := by
  have hProfile := sixColorProfileEnergy_le_four_initialResidualEnergy H N hN beta hbeta (BCFRep (Obs x))
  have hSplit := jointTransferLocalEnergyOn_add_compl H N hN beta hbeta x s
  have hLocal := jointTransferLocalEnergyOn_le_card_l2Envelope H N hN beta hbeta x s
  nlinarith

/-- Conditional finite-support consequence of SIGNED source cancellation.
The cancellation premise is not established for the frozen family in this file. -/
theorem jointTransferProfileEnergy_le_card_of_kernelCancellation (x : PairL2) (s : Finset Link)
    (hcancel : ∀ e, e ∉ s → ∀ᵐ z ∂μJ, ∀ᵐ g ∂Nu z.1 z.2 e,
      jointTransferLinkDifference H N hN beta hbeta x e z g = 0) :
    Profile (BCFRep (Obs x)) ≤ (2 / 3 : ℝ) * (s.card : ℝ) *
      (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  have hExterior : Local x sᶜ = 0 := by
    unfold jointTransferLocalEnergyOn
    have hz : (∑ e ∈ sᶜ, jointTransferLinkLocalEnergy H N hN beta hbeta x e) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact jointTransferLinkLocalEnergy_eq_zero_of_ae_kernelCancellation H N hN beta hbeta x e
        (hcancel e (Finset.mem_compl.mp he))
    rw [hz, mul_zero]
  simpa only [hExterior, mul_zero, add_zero] using
    jointTransferProfileEnergy_le_localEnvelope_add_exterior H N hN beta hbeta x s

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
local notation "Local" => jointTransferLocalEnergyOn Hn 2 Pos (beta n) (hbeta n)

/-- Exact link-local formula for the ORIGINAL frozen vector, including r=0.
The orbit remains at beta(n+1); the last transfer and half-density use beta n. -/
theorem fineFrozenInitialEnergy_eq_linkLocal :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n) FrozenVec = Local Orbit Finset.univ := by
  rw [jointTransferLocalEnergyOn_univ_eq_initial,
    ← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  simp only [fineFrozenBCF]

/-- Original frozen family with an exact, not estimated, exterior contribution. -/
theorem fineFrozenProfileEnergy_le_localEnvelope_add_exterior (s : Finset Link) :
    FrozenEnergy ≤ (2 / 3 : ℝ) * (s.card : ℝ) *
      ((kernelRightVariationRate (beta n)) ^ 2 * ‖NormTransfer (pairAbsoluteInput Hn 2 Orbit)‖ ^ 2) +
      4 * Local Orbit sᶜ := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  rw [← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  exact jointTransferProfileEnergy_le_localEnvelope_add_exterior Hn 2 Pos (beta n) (hbeta n) Orbit s

end FrozenFamily

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
