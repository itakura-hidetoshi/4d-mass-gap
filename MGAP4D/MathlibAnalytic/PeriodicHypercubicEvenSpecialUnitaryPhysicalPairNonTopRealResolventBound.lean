import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealSpectrumResolvent
import Mathlib.Topology.Algebra.Module.Equiv
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
  have hres : lambda ∈ resolventSet ℝ SN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_mem_realResolventSet_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda
  change IsUnit (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) at hres
  exact hres

/-- The unit witnessing invertibility of the real shifted non-top transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftUnit
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    (NN →L[ℝ] NN)ˣ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_isUnit_of_factor_lt_abs
    H N hN beta hbeta lambda hlambda).unit

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftUnit_coe
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftUnit
        H N hN beta hbeta lambda hlambda : (NN →L[ℝ] NN)ˣ) : NN →L[ℝ] NN) =
      algebraMap ℝ (NN →L[ℝ] NN) lambda - SN := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_isUnit_of_factor_lt_abs
      H N hN beta hbeta lambda hlambda).unit_spec

/-- The real shifted transfer outside the contraction disk, bundled directly
from its algebraic unit as a continuous linear equivalence. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    NN ≃L[ℝ] NN :=
  ContinuousLinearEquiv.ofUnit
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftUnit
      H N hN beta hbeta lambda hlambda)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv_apply
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (x : NN) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv
        H N hN beta hbeta lambda hlambda x =
      lambda • x - SN x := by
  change
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftUnit
        H N hN beta hbeta lambda hlambda : (NN →L[ℝ] NN)ˣ) : NN →L[ℝ] NN) x = _
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftUnit_coe]
  rfl

/-- Outside the finite-volume non-top contraction disk, the shifted completed
non-top transfer is bijective. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_bijective_of_factor_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    Function.Bijective
      (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN) := by
  let E : NN ≃L[ℝ] NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv
      H N hN beta hbeta lambda hlambda
  constructor
  · intro x y hxy
    apply E.injective
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv_apply,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv_apply]
    change lambda • x - SN x = lambda • y - SN y at hxy
    exact hxy
  · intro y
    refine ⟨E.symm y, ?_⟩
    change lambda • E.symm y - SN (E.symm y) = y
    simpa only [E,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv_apply] using
      E.apply_symm_apply y

/-- The finite-volume completed non-top real resolvent operator at a scalar
strictly outside the contraction disk. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) :
    NN →L[ℝ] NN :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv
      H N hN beta hbeta lambda hlambda).symm : NN →L[ℝ] NN)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_apply
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda hlambda y =
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv
        H N hN beta hbeta lambda hlambda).symm y :=
  rfl

/-- Applying the shifted transfer to its bundled real resolvent recovers the
input vector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShift_realResolvent
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    lambda •
        periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda hlambda y -
      SN
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda hlambda y) = y := by
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv_apply] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realShiftEquiv
      H N hN beta hbeta lambda hlambda).apply_symm_apply y

/-- Sharp pointwise finite-volume real resolvent estimate in reciprocal-distance
form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent_norm_bound
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
        H N hN beta hbeta lambda hlambda y‖ ≤
      (|lambda| - ‖R‖)⁻¹ * ‖y‖ := by
  let x : NN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
      H N hN beta hbeta lambda hlambda y
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
        H N hN beta hbeta lambda hlambda‖ ≤
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
      H N hN beta hbeta lambda hlambda
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
  change lambda • x - SN x = lambda • G y - SN (G y)
  rw [hx, hG]

/-- Audit-visible finite-volume real resolvent bound package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopRealResolventBoundPackage :
    Prop where
  shiftedBijective :
    ∀ (lambda : ℝ), ‖R‖ < |lambda| →
      Function.Bijective
        (algebraMap ℝ (NN →L[ℝ] NN) lambda - SN)
  rightInverse :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN),
      lambda •
          periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
            H N hN beta hbeta lambda hlambda y -
        SN
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
            H N hN beta hbeta lambda hlambda y) = y
  pointwiseResolventBound :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|) (y : NN),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda hlambda y‖ ≤
        (|lambda| - ‖R‖)⁻¹ * ‖y‖
  operatorResolventBound :
    ∀ (lambda : ℝ) (hlambda : ‖R‖ < |lambda|),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_realResolvent
          H N hN beta hbeta lambda hlambda‖ ≤
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
