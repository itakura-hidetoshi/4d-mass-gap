import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

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

/-- Outside the finite-volume contraction disk, the native real resolvent is a
right inverse for the shifted completed non-top transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_resolvent
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    lambda • (resolvent SN lambda) y - SN ((resolvent SN lambda) y) = y := by
  have hres : lambda ∈ resolventSet ℝ SN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda
  have hmul :
      (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) * resolvent SN lambda = 1 := by
    unfold resolvent
    exact Ring.mul_inverse_cancel _ hres
  have happly := congrArg (fun F : NN →L[ℝ] NN => F y) hmul
  simpa [ContinuousLinearMap.algebraMap_apply] using happly

/-- Sharp pointwise finite-volume real resolvent estimate in reciprocal-distance
form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    ‖(resolvent SN lambda) y‖ ≤ (|lambda| - ‖R‖)⁻¹ * ‖y‖ := by
  let x : NN := (resolvent SN lambda) y
  have hcoerc :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_shifted_coercive
      H N hN beta hbeta lambda x
  have hshift : lambda • x - SN x = y := by
    dsimp [x]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_resolvent
        H N hN beta hbeta lambda hlambda y
  rw [hshift] at hcoerc
  have hpositive : 0 < |lambda| - ‖R‖ := sub_pos.mpr hlambda
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hpositive).2
  simpa [x, mul_comm] using hcoerc

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
