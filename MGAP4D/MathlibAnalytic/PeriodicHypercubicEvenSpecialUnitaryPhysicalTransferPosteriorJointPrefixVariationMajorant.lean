import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointStageResidualEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanVariationIteration
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalFixedRightResponseBridge
import Mathlib.Tactic

/-!
# Constructed posterior prefix variation and genuine joint residual majorants

A chronological finite schedule transports an INITIAL right-link variation
profile by v'_s = 0 on the updated target and v'_s = v_s + c_{t,s} v_t otherwise.
The existing one-link influence estimate and compact midpoint recentering
prove the bound after every prefix. Each intermediate observable is the
actual Feller function at a fixed left boundary, not a representative chosen
from an L2 a.e. identity.

Restriction of a joint BCF to each left boundary is a BCF. Its chronological
Feller schedule equals the literal joint posterior schedule pointwise. We
average its constructed one-link oscillation against the actual posterior
probability law to obtain a pointwise residual bound. PR #5212 then gives the
stage energy bound with coefficient one on the unchanged genuine joint law.

The canonical specialization constructs the influence data from the existing
fixed-right half-barrier response envelope. Its coefficients are independent
of the left boundary. A final corollary constructs the initial profile 2||F||
for every joint BCF without any oscillation hypothesis. Sharper initial
profiles remain accepted; the final residual bound is never assumed.

Empty schedules and repeated targets are allowed, in chronological order.
No strict contraction, support-distance tail, volume-uniform bound on the
iterated profile, six-color profile adapter, physical-transfer identity, or
continuum claim is asserted. In particular s >= 1 and the half-barrier cutoff
are not the strict-Dobrushin s > 8 interval. Both existing no-go results remain.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

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

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
local notation "VariationBound" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound H N
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "Raw" => posteriorSchedule H N hN beta hbeta

/-- One chronological variation update, with the exact zero diagonal. -/
def posteriorVariationStep (c : Link → Link → ℝ) (v : Link → ℝ)
    (target source : Link) : ℝ := by
  classical
  exact if source = target then 0 else v source + c target source * v target

/-- Deterministic variation transport in the same head-first order as Raw. -/
def posteriorVariationSchedule (c : Link → Link → ℝ)
    (pre : List Link) (v : Link → ℝ) : Link → ℝ :=
  pre.foldl (fun w target => posteriorVariationStep H c w target) v

/-- Nonnegative influences preserve nonnegative prefix profiles. -/
theorem posteriorVariationSchedule_nonneg (c : Link → Link → ℝ)
    (hc : ∀ target source, 0 ≤ c target source) (pre : List Link)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source) :
    ∀ source, 0 ≤ posteriorVariationSchedule H c pre v source := by
  induction pre generalizing v with
  | nil => exact hv
  | cons target pre ih =>
      change ∀ source, 0 ≤ posteriorVariationSchedule H c pre
        (posteriorVariationStep H c v target) source
      apply ih
      intro source
      unfold posteriorVariationStep
      split_ifs
      · exact le_rfl
      · exact add_nonneg (hv source) (mul_nonneg (hc target source) (hv target))

/-- Appending a target erases that target's current variation exactly. -/
theorem posteriorVariationSchedule_append_target (c : Link → Link → ℝ)
    (pre : List Link) (target : Link) (v : Link → ℝ) :
    posteriorVariationSchedule H c (pre ++ [target]) v target = 0 := by
  simp [posteriorVariationSchedule, List.foldl_append, posteriorVariationStep]

/-- The existing Feller maps composed chronologically at a fixed left boundary. -/
def posteriorSliceSchedule (B : Cfg) (pre : List Link)
    (O : BoundedContinuousFunction Cfg ℝ) : BoundedContinuousFunction Cfg ℝ :=
  pre.foldl
    (fun G target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
        H N hN beta hbeta B target G) O

/-- The initial variation bound is propagated, with midpoint recentering at
EVERY step and with no enlargement of the carried one-link variation. -/
theorem posteriorSliceSchedule_variation_abs_le
    (B : Cfg)
    (D : PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B)
    (pre : List Link) (O : BoundedContinuousFunction Cfg ℝ)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (hV : ∀ (source : Link) (A C : Cfg), Agree A C source → |O A - O C| ≤ v source) :
    ∀ (source : Link) (A C : Cfg), Agree A C source →
      |posteriorSliceSchedule H N hN beta hbeta B pre O A -
        posteriorSliceSchedule H N hN beta hbeta B pre O C| ≤
      posteriorVariationSchedule H D.influence pre v source := by
  induction pre generalizing O v with
  | nil => exact hV
  | cons target pre ih =>
      let P : VariationBound (fun A => O A) :=
        { variation := v, variation_nonneg := hv, variation_bound := hV }
      let O' :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O
      let v' := posteriorVariationStep H D.influence v target
      have hv' : ∀ source, 0 ≤ v' source := by
        intro source
        exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_nonneg
          D v hv target source
      have hV' : ∀ (source : Link) (A C : Cfg),
          Agree A C source → |O' A - O' C| ≤ v' source := by
        intro source A C hAgree
        simpa only [O',
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply] using
          (P.toCenteredVariationProfile.conditionalExpectationVariationBound D target).variation_bound
            source A C hAgree
      change ∀ (source : Link) (A C : Cfg), Agree A C source →
        |posteriorSliceSchedule H N hN beta hbeta B pre O' A -
          posteriorSliceSchedule H N hN beta hbeta B pre O' C| ≤
        posteriorVariationSchedule H D.influence pre v' source
      exact ih (O := O') (v := v') hv' hV'

/-- Literal equality on one fixed-left slice is preserved at each integral.
The joint function here need not be continuous; regularity is carried by O. -/
theorem posteriorSliceSchedule_eq_posteriorSchedule (B : Cfg) (pre : List Link)
    (F : Joint → ℝ) (O : BoundedContinuousFunction Cfg ℝ)
    (hO : ∀ A, O A = F (B, A)) :
    ∀ A, posteriorSliceSchedule H N hN beta hbeta B pre O A = Raw pre F (B, A) := by
  induction pre generalizing F O with
  | nil => exact hO
  | cons target pre ih =>
      change ∀ A,
        posteriorSliceSchedule H N hN beta hbeta B pre
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
            H N hN beta hbeta B target O) A =
        Raw pre (posteriorMean H N hN beta hbeta target F) (B, A)
      apply ih (F := posteriorMean H N hN beta hbeta target F)
        (O := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF
          H N hN beta hbeta B target O)
      intro A
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationContinuousBCF_apply,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral]
      unfold posteriorMean
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => hO (Function.update A target g))

/-- A genuine joint BCF restricted to a fixed left boundary. -/
def posteriorLeftSectionBCF (F : BoundedContinuousFunction Joint ℝ) (B : Cfg) :
    BoundedContinuousFunction Cfg ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A => F (B, A), F.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Every literal intermediate has continuous fixed-left sections. This is
proved from the Feller construction, not inferred from joint a.e. equality. -/
theorem posteriorSchedule_left_continuous (pre : List Link)
    (F : BoundedContinuousFunction Joint ℝ) (B : Cfg) :
    Continuous (fun A => Raw pre F (B, A)) := by
  let O := posteriorLeftSectionBCF H N F B
  have heq : (fun A => Raw pre F (B, A)) =
      fun A => posteriorSliceSchedule H N hN beta hbeta B pre O A := by
    funext A
    exact (posteriorSliceSchedule_eq_posteriorSchedule
      H N hN beta hbeta B pre F O (fun _ => rfl) A).symm
  rw [heq]
  exact (posteriorSliceSchedule H N hN beta hbeta B pre O).continuous

/-- Boundary-independent response coefficients propagate a uniform INITIAL
joint BCF right-link profile to the actual pointwise prefix observables. -/
theorem posteriorSchedule_variation_abs_le (R : ResponseData)
    (pre : List Link) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (hV : ∀ (B : Cfg) (source : Link) (A C : Cfg),
      Agree A C source → |F (B, A) - F (B, C)| ≤ v source)
    (B : Cfg) (source : Link) (A C : Cfg) (hAgree : Agree A C source) :
    |Raw pre F (B, A) - Raw pre F (B, C)| ≤
      posteriorVariationSchedule H
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
          H beta R.epsilon) pre v source := by
  let O := posteriorLeftSectionBCF H N F B
  have h := posteriorSliceSchedule_variation_abs_le
    H N hN beta hbeta B (R.toNonstrictInfluenceData B) pre O v hv (hV B)
      source A C hAgree
  rw [posteriorSliceSchedule_eq_posteriorSchedule
      H N hN beta hbeta B pre F O (fun _ => rfl) A,
    posteriorSliceSchedule_eq_posteriorSchedule
      H N hN beta hbeta B pre F O (fun _ => rfl) C] at h
  exact h

/-- Averaging the propagated pointwise variation constructs the literal
residual bound. Fiber continuity supplies the integrability used by the
probability integral estimate. There is no final residual hypothesis. -/
theorem posteriorStageResidual_abs_le_variationSchedule (R : ResponseData)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (hV : ∀ (B : Cfg) (source : Link) (A C : Cfg),
      Agree A C source → |F (B, A) - F (B, C)| ≤ v source) (z : Joint) :
    |posteriorStageResidual H N hN beta hbeta pre target F z| ≤
      posteriorVariationSchedule H
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
          H beta R.epsilon) pre v target := by
  classical
  let G : Cfg → ℝ := fun A => Raw pre F (z.1, A)
  let delta := posteriorVariationSchedule H
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
      H beta R.epsilon) pre v target
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta z.1 z.2 target
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta z.1 z.2 target
  have hUpdate : Continuous (fun g : GaugeT => Function.update z.2 target g) := by
    apply continuous_pi
    intro e
    by_cases he : e = target
    · subst e
      simpa only [Function.update_same] using
        (continuous_id : Continuous (fun g : GaugeT => g))
    · simpa only [Function.update_of_ne he] using
        (continuous_const : Continuous (fun _ : GaugeT => z.2 e))
  have hFiber : Continuous (fun g : GaugeT => G (Function.update z.2 target g)) :=
    (posteriorSchedule_left_continuous H N hN beta hbeta pre F z.1).comp hUpdate
  have hOsc : ∀ g : GaugeT, |G z.2 - G (Function.update z.2 target g)| ≤ delta := by
    intro g
    apply posteriorSchedule_variation_abs_le H N hN beta hbeta R pre F v hv hV
    intro e he
    rw [Function.update_of_ne he]
  have hIntegral :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalIntegral_direct_difference_abs_le
      H N hN beta hbeta z.1 z.2 target
      (fun _ : GaugeT => G z.2) (fun g : GaugeT => G (Function.update z.2 target g))
      continuous_const hFiber delta hOsc
  change |(∫ _ : GaugeT, G z.2 ∂mu) -
    (∫ g : GaugeT, G (Function.update z.2 target g) ∂mu)| ≤ delta at hIntegral
  have hConst : (∫ _ : GaugeT, G z.2 ∂mu) = G z.2 := by simp
  rw [hConst] at hIntegral
  change |Raw pre F z - Raw (pre ++ [target]) F z| ≤ delta
  rw [posteriorSchedule_append_singleton]
  change |G z.2 - (∫ g : GaugeT, G (Function.update z.2 target g) ∂mu)| ≤ delta
  exact hIntegral

/-- Coefficient-one stage energy from the constructed prefix variation. -/
theorem posteriorStageResidualEnergy_le_variationSchedule_sq (R : ResponseData)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (hV : ∀ (B : Cfg) (source : Link) (A C : Cfg),
      Agree A C source → |F (B, A) - F (B, C)| ≤ v source) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F ≤
      posteriorVariationSchedule H
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
          H beta R.epsilon) pre v target ^ 2 := by
  apply posteriorStageResidualEnergy_le_of_ae_bound
    H N hN beta hbeta pre target F F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  · exact posteriorVariationSchedule_nonneg H _
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_nonneg
        H beta R.epsilon R.epsilon_nonneg) pre v hv target
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using
        posteriorStageResidual_abs_le_variationSchedule H N hN beta hbeta R pre target F v hv hV z

/-- Actual canonical prefix profile on the existing half-barrier interval.
The left-boundary parameter is absent because the response matrix is uniform. -/
def canonicalPosteriorPrefixVariation (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (pre : List Link) (v : Link → ℝ) : Link → ℝ :=
  posteriorVariationSchedule H
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence H beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
        H N hN s hs beta hbeta hcut).epsilon) pre v

/-- The final pointwise bound uses the actual canonical influence data. Only
an INITIAL variation profile is supplied by the observable. -/
theorem posteriorStageResidual_abs_le_canonicalPrefixVariation
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (hV : ∀ (B : Cfg) (source : Link) (A C : Cfg),
      Agree A C source → |F (B, A) - F (B, C)| ≤ v source) (z : Joint) :
    |posteriorStageResidual H N hN beta hbeta pre target F z| ≤
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut pre v target :=
  posteriorStageResidual_abs_le_variationSchedule H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut) pre target F v hv hV z

/-- Exact joint stage energy controlled by the actual canonical prefix profile. -/
theorem posteriorStageResidualEnergy_le_canonicalPrefixVariation_sq
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (hV : ∀ (B : Cfg) (source : Link) (A C : Cfg),
      Agree A C source → |F (B, A) - F (B, C)| ≤ v source) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F ≤
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut pre v target ^ 2 :=
  posteriorStageResidualEnergy_le_variationSchedule_sq H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut) pre target F v hv hV

/-- A concrete initial profile exists for every joint BCF, without any
pointwise variation or final residual assumption. -/
theorem jointBCF_variation_le_two_norm (F : BoundedContinuousFunction Joint ℝ)
    (B A C : Cfg) : |F (B, A) - F (B, C)| ≤ 2 * ‖F‖ := by
  calc
    |F (B, A) - F (B, C)| ≤ |F (B, A)| + |F (B, C)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (F (B, A)) (-(F (B, C)))
    _ ≤ ‖F‖ + ‖F‖ := add_le_add
      (by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (B, A))
      (by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (B, C))
    _ = 2 * ‖F‖ := by ring

/-- Fully constructed finite-prefix energy majorant for any joint BCF. This
fallback is finite, but is not asserted to be small or uniform in volume. -/
theorem posteriorStageResidualEnergy_le_canonicalUniformPrefixVariation_sq
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (pre : List Link) (target : Link) (F : BoundedContinuousFunction Joint ℝ) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F ≤
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut pre
        (fun _ => 2 * ‖F‖) target ^ 2 := by
  apply posteriorStageResidualEnergy_le_canonicalPrefixVariation_sq
    H N hN beta hbeta s hs hcut pre target F (fun _ => 2 * ‖F‖)
  · intro source
    exact mul_nonneg (by norm_num) (norm_nonneg F)
  · intro B source A C hAgree
    exact jointBCF_variation_le_two_norm H N F B A C

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
