import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointFiniteSchedule
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepVectorTelescoping
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

/-!
# Literal posterior stage residuals and exact projection energy

For a finite chronological prefix pre and next target e, define the literal
residual R = M_pre F - M_e(M_pre F). PR #5211 identifies both terms with the
existing joint L2 projection schedule. Their difference therefore represents
(I - P_e) S_pre [F], without assuming pointwise equality of L2 representatives.

The squared residual is integrable on the bounded strongly measurable core,
and its integral is exactly the squared norm of that existing projection
residual. Orthogonality gives the one-step Pythagorean norm loss. An a.e. L2
majorant of the literal residual transfers with coefficient one; a constant
delta gives the bound delta^2 under the genuine joint probability measure.

The majorant itself is an explicit hypothesis, not a newly proved Dobrushin
profile or spatial decay rate. The prefix and next target may repeat links;
no commutation between distinct targets is assumed. We do not identify the
sum of noncommuting stage energies with the squared total vector defect.
No new law, Hilbert carrier, cutoff, or Euclidean-time interpretation is used.
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

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Raw" => posteriorSchedule H N hN beta hbeta
local notation "StageL2" => posteriorScheduleL2 H N hN beta hbeta

/-- Appending a target applies its literal posterior integral after the prefix. -/
theorem posteriorSchedule_append_singleton (pre : List Link) (target : Link)
    (F : Joint → ℝ) :
    Raw (pre ++ [target]) F = posteriorMean H N hN beta hbeta target (Raw pre F) := by
  simp only [posteriorSchedule, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The existing L2 class after one more update is the actual joint projection. -/
theorem posteriorScheduleL2_append_singleton (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    StageL2 (pre ++ [target]) F hF bound hbound =
      PJoint target (StageL2 pre F hF bound hbound) := by
  simp only [posteriorScheduleL2_eq_projectionSchedule, realHilbertProjectionSweep_append,
    realHilbertProjectionSweep, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

/-- Literal difference between the prefix integral and its next posterior update. -/
def posteriorStageResidual (pre : List Link) (target : Link)
    (F : Joint → ℝ) (z : Joint) : ℝ :=
  Raw pre F z - Raw (pre ++ [target]) F z

/-- Squared energy of the literal residual under the original joint law. -/
def posteriorStageResidualEnergy (pre : List Link) (target : Link)
    (F : Joint → ℝ) : ℝ :=
  ∫ z, posteriorStageResidual H N hN beta hbeta pre target F z ^ 2 ∂μJ

/-- The actual projection residual has the literal stage residual as a.e.
representative. The statement is valid at every finite chronological prefix. -/
theorem projectionStageResidual_coeFn_eq_posteriorStageResidual
    (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z => (StageL2 pre F hF bound hbound -
      PJoint target (StageL2 pre F hF bound hbound)) z) =ᵐ[μJ]
        posteriorStageResidual H N hN beta hbeta pre target F := by
  let x : JL2 := StageL2 pre F hF bound hbound
  let y : JL2 := StageL2 (pre ++ [target]) F hF bound hbound
  have hy : y = PJoint target x :=
    posteriorScheduleL2_append_singleton H N hN beta hbeta pre target F hF bound hbound
  have hxRep : (fun z => x z) =ᵐ[μJ] Raw pre F :=
    MemLp.coeFn_toLp
      (posteriorSchedule_memLp_two H N hN beta hbeta pre F hF bound hbound)
  have hyRep : (fun z => y z) =ᵐ[μJ] Raw (pre ++ [target]) F :=
    MemLp.coeFn_toLp
      (posteriorSchedule_memLp_two H N hN beta hbeta (pre ++ [target]) F hF bound hbound)
  change (fun z => (x - PJoint target x) z) =ᵐ[μJ] _
  rw [← hy]
  filter_upwards [Lp.coeFn_sub x y, hxRep, hyRep] with z hs hxz hyz
  change (x - y) z = Raw pre F z - Raw (pre ++ [target]) F z
  calc
    (x - y) z = x z - y z := hs
    _ = _ := by rw [hxz, hyz]

/-- L2 membership follows from the two already identified finite schedules. -/
theorem posteriorStageResidual_memLp_two (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    MemLp (posteriorStageResidual H N hN beta hbeta pre target F) 2 μJ := by
  change MemLp (Raw pre F - Raw (pre ++ [target]) F) 2 μJ
  exact (posteriorSchedule_memLp_two H N hN beta hbeta pre F hF bound hbound).sub
    (posteriorSchedule_memLp_two H N hN beta hbeta (pre ++ [target]) F hF bound hbound)

/-- The displayed squared-energy integral is a genuine integrable quantity. -/
theorem posteriorStageResidual_sq_integrable (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    Integrable (fun z => posteriorStageResidual H N hN beta hbeta pre target F z ^ 2) μJ :=
  (posteriorStageResidual_memLp_two H N hN beta hbeta pre target F hF bound hbound).integrable_sq

/-- Exact energy identity; no density-comparison constant is introduced. -/
theorem posteriorStageResidualEnergy_eq_projectionResidualNormSq
    (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F =
      ‖StageL2 pre F hF bound hbound -
        PJoint target (StageL2 pre F hF bound hbound)‖ ^ 2 := by
  let r : JL2 := StageL2 pre F hF bound hbound -
    PJoint target (StageL2 pre F hF bound hbound)
  have hr : (fun z => r z) =ᵐ[μJ]
      posteriorStageResidual H N hN beta hbeta pre target F :=
    projectionStageResidual_coeFn_eq_posteriorStageResidual
      H N hN beta hbeta pre target F hF bound hbound
  change (∫ z, posteriorStageResidual H N hN beta hbeta pre target F z ^ 2 ∂μJ) = ‖r‖ ^ 2
  calc
    _ = ∫ z, r z ^ 2 ∂μJ :=
      integral_congr_ae (hr.mono fun z hz => congrArg (fun t : ℝ => t ^ 2) hz.symm)
    _ = ‖r‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
        (L2.inner_def (𝕜 := ℝ) r r).symm

/-- One-step Pythagorean loss, with the chronological prefix unchanged. -/
theorem posteriorStageResidualEnergy_eq_norm_loss (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F =
      ‖StageL2 pre F hF bound hbound‖ ^ 2 -
        ‖StageL2 (pre ++ [target]) F hF bound hbound‖ ^ 2 := by
  rw [posteriorStageResidualEnergy_eq_projectionResidualNormSq
    H N hN beta hbeta pre target F hF bound hbound,
    posteriorScheduleL2_append_singleton H N hN beta hbeta pre target F hF bound hbound]
  let x : JL2 := StageL2 pre F hF bound hbound
  let p : JL2 := PJoint target x
  have hm := periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
    H N target
  have hp : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N target]
      (fun z => p z) μJ :=
    aestronglyMeasurable_condExpL2 (𝕜 := ℝ) hm x
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm x p hp
  have horth : inner ℝ (x - p) p = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hi.symm
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - p) p horth
  rw [sub_add_cancel] at hpyth
  change ‖x - p‖ ^ 2 = ‖x‖ ^ 2 - ‖p‖ ^ 2
  linarith

/-- Nonnegativity does not require integrability because the integrand is a square. -/
theorem posteriorStageResidualEnergy_nonneg (pre : List Link) (target : Link)
    (F : Joint → ℝ) :
    0 ≤ posteriorStageResidualEnergy H N hN beta hbeta pre target F :=
  integral_nonneg fun _ => sq_nonneg _

/-- Any a.e. L2 majorant of the literal residual controls the exact stage
energy with coefficient one. Producing that majorant remains a separate task. -/
theorem posteriorStageResidualEnergy_le_of_ae_majorant (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (majorant : Joint → ℝ) (hMajorant : MemLp majorant 2 μJ)
    (hdom : ∀ᵐ z ∂μJ,
      ‖posteriorStageResidual H N hN beta hbeta pre target F z‖ ≤ ‖majorant z‖) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F ≤
      ∫ z, majorant z ^ 2 ∂μJ := by
  exact integral_mono_ae
    (posteriorStageResidual_sq_integrable H N hN beta hbeta pre target F hF bound hbound)
    hMajorant.integrable_sq
    (hdom.mono fun z hz => (sq_le_sq).2 hz)

/-- Under the original probability law, a constant residual bound delta costs
exactly delta squared, not a volume or rank dependent comparison factor. -/
theorem posteriorStageResidualEnergy_le_of_ae_bound (pre : List Link) (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdom : ∀ᵐ z ∂μJ,
      ‖posteriorStageResidual H N hN beta hbeta pre target F z‖ ≤ delta) :
    posteriorStageResidualEnergy H N hN beta hbeta pre target F ≤ delta ^ 2 := by
  letI : IsProbabilityMeasure μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have hConst : MemLp (fun _ : Joint => delta) 2 μJ := memLp_const delta
  have hdom' : ∀ᵐ z ∂μJ,
      ‖posteriorStageResidual H N hN beta hbeta pre target F z‖ ≤
        ‖(fun _ : Joint => delta) z‖ :=
    hdom.mono fun z hz => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hdelta] using hz
  simpa using posteriorStageResidualEnergy_le_of_ae_majorant
    H N hN beta hbeta pre target F hF bound hbound (fun _ => delta) hConst hdom'

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
