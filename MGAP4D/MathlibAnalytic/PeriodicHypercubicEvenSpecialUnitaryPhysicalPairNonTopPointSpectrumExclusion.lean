import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferCoercivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairNonTopPointSpectrumTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairNonTopPointSpectrumCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairNonTopPointSpectrumSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairNonTopPointSpectrumMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairNonTopPointSpectrumBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairNonTopPointSpectrumSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairNonTopPointSpectrumSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section NonTopPointSpectrumExclusion

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- Quantitative shifted residual bound for the completed finite-volume non-top
transfer.  It is useful even when the coefficient on the left is nonpositive;
for `‖R‖ < |lambda|` it becomes a genuine coercive lower bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_shifted_coercive
    (lambda : ℝ) (x : NN) :
    (|lambda| - ‖R‖) * ‖x‖ ≤ ‖lambda • x - SN x‖ := by
  have hSNop : ‖SN‖ ≤ ‖R‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
      H N hN beta hbeta
  have hApply0 : ‖SN x‖ ≤ ‖SN‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        H N hN beta hbeta) x
  have hApply : ‖SN x‖ ≤ ‖R‖ * ‖x‖ :=
    hApply0.trans
      (mul_le_mul_of_nonneg_right hSNop (norm_nonneg x))
  have htri := norm_add_le (lambda • x - SN x) (SN x)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs] at htri
  nlinarith

/-- If the modulus of a real scalar lies strictly outside the finite-volume
non-top contraction disk, it cannot have a nonzero eigenvector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvector_eq_zero_of_norm_lt_abs
    (lambda : ℝ) (hlambda : ‖R‖ < |lambda|)
    (x : NN) (heigen : SN x = lambda • x) :
    x = 0 := by
  have hcoerc :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_shifted_coercive
      H N hN beta hbeta lambda x
  have hres : lambda • x - SN x = 0 := by
    rw [heigen]
    exact sub_self (lambda • x)
  rw [hres, norm_zero] at hcoerc
  have hdelta : 0 < |lambda| - ‖R‖ := sub_pos.mpr hlambda
  have hxnorm : ‖x‖ = 0 := by
    nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hxnorm

/-- Every real eigenvalue carried by a nonzero completed non-top vector lies in
the closed disk of radius `‖R‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvalue_abs_le_factor
    (lambda : ℝ) (x : NN) (hx : x ≠ 0)
    (heigen : SN x = lambda • x) :
    |lambda| ≤ ‖R‖ := by
  by_contra hle
  have hgt : ‖R‖ < |lambda| := lt_of_not_ge hle
  have hxzero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvector_eq_zero_of_norm_lt_abs
      H N hN beta hbeta lambda hgt x heigen
  exact hx hxzero

/-- Hence every real eigenvalue on a nonzero completed non-top vector has modulus
strictly below one at each fixed finite volume. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvalue_abs_lt_one
    (lambda : ℝ) (x : NN) (hx : x ≠ 0)
    (heigen : SN x = lambda • x) :
    |lambda| < 1 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvalue_abs_le_factor
      H N hN beta hbeta lambda x hx heigen).trans_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta)

/-- In particular the real unit circle carries no nonzero eigenvector in the
completed non-top sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_unit_modulus_eigenvector_eq_zero
    (lambda : ℝ) (hlambda : |lambda| = 1)
    (x : NN) (heigen : SN x = lambda • x) :
    x = 0 := by
  have hq : ‖R‖ < |lambda| := by
    rw [hlambda]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvector_eq_zero_of_norm_lt_abs
      H N hN beta hbeta lambda hq x heigen

/-- Audit-visible finite-volume real point-spectrum exclusion package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPointSpectrumExclusionPackage :
    Prop where
  shiftedCoercive :
    ∀ (lambda : ℝ) (x : NN),
      (|lambda| - ‖R‖) * ‖x‖ ≤ ‖lambda • x - SN x‖
  outsideDiskZero :
    ∀ (lambda : ℝ), ‖R‖ < |lambda| →
      ∀ x : NN, SN x = lambda • x → x = 0
  eigenvalueBound :
    ∀ (lambda : ℝ) (x : NN), x ≠ 0 → SN x = lambda • x →
      |lambda| ≤ ‖R‖
  strictEigenvalueBound :
    ∀ (lambda : ℝ) (x : NN), x ≠ 0 → SN x = lambda • x →
      |lambda| < 1
  unitModulusExcluded :
    ∀ (lambda : ℝ), |lambda| = 1 →
      ∀ x : NN, SN x = lambda • x → x = 0

/-- Construct the finite-volume real point-spectrum exclusion package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPointSpectrumExclusionPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPointSpectrumExclusionPackage
      H N hN beta hbeta :=
  { shiftedCoercive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_shifted_coercive
        H N hN beta hbeta
    outsideDiskZero :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvector_eq_zero_of_norm_lt_abs
        H N hN beta hbeta
    eigenvalueBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvalue_abs_le_factor
        H N hN beta hbeta
    strictEigenvalueBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_eigenvalue_abs_lt_one
        H N hN beta hbeta
    unitModulusExcluded :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_unit_modulus_eigenvector_eq_zero
        H N hN beta hbeta }

end NonTopPointSpectrumExclusion

end

end MathlibAnalytic
end MGAP4D
