import MGAP4D.MathlibAnalytic.HilbertTensorContinuousMap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance osBoundaryExcitationNativeHilbertTensorTransferSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationNativeHilbertTensorTransferSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationNativeHilbertTensorTransferSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationNativeHilbertTensorTransferSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationNativeHilbertTensorTransferSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationNativeHilbertTensorTransferSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationNativeHilbertTensorTransferSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Mathlib's native Hilbert-tensor norm on the physical excitation tensor
carrier, kept local to this file so that it does not replace the canonical
algebraic tensor module path used by the concrete pair-`L²` embedding. -/
@[reducible] local instance osBoundaryExcitationNativeHilbertTensorTransferNormedAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

/-- The matching native Mathlib tensor inner product, again intentionally file-local. -/
@[reducible] local instance osBoundaryExcitationNativeHilbertTensorTransferInnerProductSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

/-- Tensor-square a single bounded operator on the physical one-slice
excitation Hilbert space. -/
@[reducible] noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (T : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta :=
  hilbertTensorMap
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (G := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (H := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    T T

/-- The continuous two-endpoint excitation transfer on Mathlib's native
Hilbert tensor norm. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorMap
    H N hN beta hbeta
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n)

/-- Exact definitional receipt exposing the typed physical tensor-square wrapper. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_map
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorMap
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) :=
  rfl

/-- Exact receipt exposing the generic Hilbert tensor map underlying the transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_hilbertTensorMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n =
      hilbertTensorMap
        (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)
        (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)
        (G := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)
        (H := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n)
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) :=
  rfl

/-- On decomposable tensors the native continuous transfer is exactly the
expected two-factor transfer power. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f) ⊗ₜ[ℝ]
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g) := by
  rfl

/-- At Euclidean time zero the native Hilbert-tensor transfer is the identity. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta 0 =
      ContinuousLinearMap.id ℝ
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer,
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorMap]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- The native Hilbert-tensor transfer is an exact discrete semigroup on the
whole algebraic Hilbert tensor carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta (m + n) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta m ∘L
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer,
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorMap, pow_add]
  | add x y hx hy =>
      simp only [map_add, ContinuousLinearMap.comp_apply, hx, hy]

/-- Pointwise form of the native Hilbert-tensor semigroup law. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_add_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta (m + n) x =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta m
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n x) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_add]
  rfl

/-- The tensor-transfer operator norm is bounded by the product of the two
one-slice operator norms.  The right-tensor estimate is rebuilt pointwise on
the exact physical carrier to avoid a large dependent `isDefEq` comparison. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n) ≤
      ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) ^ n‖ *
      ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) ^ n‖ := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta
  let T : K →L[ℝ] K :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_hilbertTensorMap]
  unfold hilbertTensorMap
  have hR : ContinuousLinearMap.opNorm (hilbertTensorRTensor T K) ≤ ‖T‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    exact hilbertTensorRTensor_bound (E := K) (F := K) (G := K) T x
  have hL : ContinuousLinearMap.opNorm (hilbertTensorLTensor T K) ≤ ‖T‖ := by
    exact hilbertTensorLTensor_norm_le (E := K) (G := K) (H := K) T
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul hR hL (norm_nonneg (hilbertTensorLTensor T K)) (norm_nonneg T)

/-- Positive Euclidean times inherit the doubled finite-volume exponential
operator-norm decay on the whole native Hilbert tensor carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n) ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hT : ‖T ^ n‖ ≤ Real.exp (-(n : ℝ) * r) := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_exp_of_pos
        H N hN beta hbeta n hn
  have hNorm : 0 ≤ ‖T ^ n‖ := norm_nonneg (T ^ n)
  have hExp : 0 ≤ Real.exp (-(n : ℝ) * r) := (Real.exp_pos _).le
  calc
    ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n) ≤ ‖T ^ n‖ * ‖T ^ n‖ := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_mul
          H N hN beta hbeta n
    _ ≤ Real.exp (-(n : ℝ) * r) * Real.exp (-(n : ℝ) * r) :=
      mul_le_mul hT hT hNorm hExp
    _ = Real.exp (-2 * (n : ℝ) * r) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Consequently every vector in the whole native Hilbert tensor carrier,
not only pure tensors, obeys the doubled exponential estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_apply_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n x‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖x‖ := by
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n x‖ ≤
      ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n) * ‖x‖ := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n).le_opNorm x
    _ ≤ Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_exp_of_pos
          H N hN beta hbeta n hn)
        (norm_nonneg x)

/-- Audit-visible receipt that the excitation tensor transfer has a bounded
native Hilbert realization, an exact semigroup law, and doubled exponential
operator decay on arbitrary algebraic tensors. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationNativeHilbertTensorTransferPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferZero :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta 0 =
      ContinuousLinearMap.id ℝ
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta)
  transferAdd :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta (m + n) =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta m ∘L
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta n
  doubledOperatorDecay :
    ∀ n : ℕ, 0 < n →
      ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n) ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta)
  doubledVectorDecay :
    ∀ (n : ℕ), 0 < n →
      ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta n x‖ ≤
          Real.exp
            (-2 * (n : ℝ) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
                H N hN beta hbeta) * ‖x‖

/-- Construct the bounded native Hilbert-tensor transfer package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationNativeHilbertTensorTransferPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationNativeHilbertTensorTransferPackage
      H N hN beta hbeta :=
  { transferZero :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_zero
        H N hN beta hbeta
    transferAdd :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_add
        H N hN beta hbeta
    doubledOperatorDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_exp_of_pos
        H N hN beta hbeta
    doubledVectorDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_apply_norm_le_exp_of_pos
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D