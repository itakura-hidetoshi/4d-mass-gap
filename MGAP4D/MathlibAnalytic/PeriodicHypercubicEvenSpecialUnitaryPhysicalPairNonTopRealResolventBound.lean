import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- Generic right-inverse identity for the native real resolvent of a continuous
linear endomorphism.  Keeping this carrier-independent avoids elaborating the
physical-pair carrier inside the algebraic inverse calculation. -/
private theorem continuousLinearMap_realShift_resolvent_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (lambda : ℝ)
    (hres : lambda ∈ resolventSet ℝ T) (y : E) :
    lambda • (resolvent T lambda) y - T ((resolvent T lambda) y) = y := by
  have hmul :
      (algebraMap ℝ (E →L[ℝ] E) lambda - T) * resolvent T lambda = 1 := by
    unfold resolvent
    exact Ring.mul_inverse_cancel _ hres
  have happly := congrArg (fun F : E →L[ℝ] E => F y) hmul
  simpa [ContinuousLinearMap.algebraMap_apply] using happly

/-- Generic reciprocal-distance resolvent estimate obtained from a shifted
coercive estimate. -/
private theorem continuousLinearMap_resolvent_norm_bound_of_shifted_coercive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (q lambda : ℝ)
    (hres : lambda ∈ resolventSet ℝ T)
    (hpositive : 0 < |lambda| - q)
    (hcoerc : ∀ x : E,
      (|lambda| - q) * ‖x‖ ≤ ‖lambda • x - T x‖)
    (y : E) :
    ‖(resolvent T lambda) y‖ ≤ (|lambda| - q)⁻¹ * ‖y‖ := by
  have h := hcoerc ((resolvent T lambda) y)
  rw [continuousLinearMap_realShift_resolvent_apply T lambda hres y] at h
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hpositive).2
  simpa [mul_comm] using h

local instance physicalPairNonTopRealResolventBoundTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairNonTopRealResolventBoundCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairNonTopRealResolventBoundSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairNonTopRealResolventBoundMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairNonTopRealResolventBoundBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairNonTopRealResolventBoundSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairNonTopRealResolventBoundSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section NonTopRealResolventBound

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- Sharp pointwise finite-volume real resolvent estimate in reciprocal-distance
form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    ‖(resolvent SN lambda) y‖ ≤ (|lambda| - ‖R‖)⁻¹ * ‖y‖ := by
  have hres : lambda ∈ resolventSet ℝ SN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda
  have hpositive : 0 < |lambda| - ‖R‖ := sub_pos.mpr hlambda
  apply
    continuousLinearMap_resolvent_norm_bound_of_shifted_coercive
      SN ‖R‖ lambda hres hpositive
  intro x
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_shifted_coercive
      H N hN beta hbeta lambda x

/-- Operator norm of the finite-volume real resolvent is controlled by the
inverse distance from `lambda` to the contraction disk. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_le
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    ‖resolvent SN lambda‖ ≤ (|lambda| - ‖R‖)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
        H N hN beta hbeta lambda hlambda

end NonTopRealResolventBound

end

end MathlibAnalytic
end MGAP4D
