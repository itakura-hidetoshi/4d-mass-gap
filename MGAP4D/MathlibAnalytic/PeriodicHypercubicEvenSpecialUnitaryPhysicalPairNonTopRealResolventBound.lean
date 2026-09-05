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

/-- Outside the finite-volume contraction disk, the real shifted non-top
transfer is a unit in the native continuous-endomorphism algebra. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_isUnit_of_factor_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    IsUnit (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda

/-- The finite-volume real resolvent is the native ring resolvent of the
completed non-top transfer.  It is defined without carrying a proof argument. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
    (lambda : ℝ) : NN →L[ℝ] NN :=
  resolvent SN lambda

/-- The shifted transfer followed by its real resolvent is the identity outside
the contraction disk. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_mul_realResolvent_eq_one
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) *
        periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda = 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
  unfold resolvent
  exact Ring.mul_inverse_cancel _
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_isUnit_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda)

/-- The real resolvent followed by the shifted transfer is also the identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_mul_realShift_eq_one
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda *
      (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) = 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
  unfold resolvent
  exact Ring.inverse_mul_cancel _
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_isUnit_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda)

/-- Applying the shifted transfer to its real resolvent recovers the input. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent_operator
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda y) = y := by
  have h := congrArg (fun F : NN →L[ℝ] NN => F y)
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_mul_realResolvent_eq_one
      H N hN beta hbeta lambda hlambda)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- Pointwise form of the shifted right-inverse identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    lambda •
        periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda y -
      SN
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda y) = y := by
  simpa [ContinuousLinearMap.algebraMap_apply] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent_operator
      H N hN beta hbeta lambda hlambda y

/-- The shifted operator is injective outside the contraction disk. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_injective_of_factor_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    Function.Injective (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) := by
  intro x y hxy
  have hleft :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_mul_realShift_eq_one
      H N hN beta hbeta lambda hlambda
  have hx := congrArg (fun F : NN →L[ℝ] NN => F x) hleft
  have hy := congrArg (fun F : NN →L[ℝ] NN => F y) hleft
  have hmap := congrArg
    (fun z : NN =>
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda z) hxy
  calc
    x = periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda
          ((algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) x) := by
      symm
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hx
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda
          ((algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) y) := hmap
    _ = y := by
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hy

/-- The shifted operator is surjective outside the contraction disk. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_surjective_of_factor_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    Function.Surjective (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) := by
  intro y
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
    H N hN beta hbeta lambda y, ?_⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent_operator
      H N hN beta hbeta lambda hlambda y

/-- Outside the finite-volume non-top contraction disk, the shifted completed
non-top transfer is bijective. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_bijective_of_factor_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    Function.Bijective (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) :=
  ⟨periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_injective_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda,
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_surjective_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda⟩

/-- Sharp pointwise finite-volume real resolvent estimate in reciprocal-distance
form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda y‖ ≤
      (|lambda| - ‖R‖)⁻¹ * ‖y‖ := by
  let x : NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
      H N hN beta hbeta lambda y
  have hcoerc :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_shifted_coercive
      H N hN beta hbeta lambda x
  have hshift : lambda • x - SN x = y := by
    dsimp [x]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent
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
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda‖ ≤
      (|lambda| - ‖R‖)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
        H N hN beta hbeta lambda hlambda

/-- The shifted finite-volume completed non-top equation has a unique solution
for every right-hand side whenever the real scalar lies outside the contraction
disk. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_existsUnique
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    ∃! x : NN, lambda • x - SN x = y := by
  let G : NN →L[ℝ] NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
      H N hN beta hbeta lambda
  have hG : lambda • G y - SN (G y) = y := by
    dsimp [G]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent
        H N hN beta hbeta lambda hlambda y
  refine ⟨G y, hG, ?_⟩
  intro x hx
  have hbij :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_bijective_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda
  apply hbij.1
  simpa [ContinuousLinearMap.algebraMap_apply] using hx.trans hG.symm

/-- Audit-visible finite-volume real resolvent bound package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealResolventBoundPackage :
    Prop where
  shiftedBijective :
    ∀ (lambda : ℝ), ‖R‖ < |lambda| →
      Function.Bijective (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN)
  rightInverse :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN),
      lambda •
          periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
            H N hN beta hbeta lambda y -
        SN
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
            H N hN beta hbeta lambda y) = y
  pointwiseResolventBound :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda y‖ ≤
        (|lambda| - ‖R‖)⁻¹ * ‖y‖
  operatorResolventBound :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda‖ ≤
        (|lambda| - ‖R‖)⁻¹
  uniqueShiftedSolution :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN),
      ∃! x : NN, lambda • x - SN x = y

/-- Construct the finite-volume real resolvent bound package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealResolventBoundPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealResolventBoundPackage
      H N hN beta hbeta :=
  { shiftedBijective :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_bijective_of_factor_lt_abs
        H N hN beta hbeta
    rightInverse :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent
        H N hN beta hbeta
    pointwiseResolventBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
        H N hN beta hbeta
    operatorResolventBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_le
        H N hN beta hbeta
    uniqueShiftedSolution :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_existsUnique
        H N hN beta hbeta }

end NonTopRealResolventBound

end

end MathlibAnalytic
end MGAP4D
