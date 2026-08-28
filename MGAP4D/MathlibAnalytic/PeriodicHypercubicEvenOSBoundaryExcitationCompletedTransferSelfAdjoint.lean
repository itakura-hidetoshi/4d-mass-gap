import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedBoundaryMatrixElement
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open UniformSpace
open scoped TensorProduct InnerProductSpace InnerProduct

noncomputable section

/-- On a complete real Hilbert space, the inner-product symmetry equation is
exactly enough to obtain Mathlib self-adjointness for a bounded endomorphism. -/
theorem continuousLinearMap_isSelfAdjoint_of_inner_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) :
    IsSelfAdjoint A := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact hA

/-- A bounded endomorphism is self-adjoint when it intertwines, along a dense
linear isometry, a symmetric bounded endomorphism on the dense source. -/
theorem continuousLinearMap_isSelfAdjoint_of_dense_linearIsometry_intertwining
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (J : E →ₗᵢ[ℝ] F)
    (hDense : DenseRange J)
    (S : E →L[ℝ] E)
    (T : F →L[ℝ] F)
    (hS : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y))
    (hIntertwine : ∀ x, T (J x) = J (S x)) :
    IsSelfAdjoint T := by
  apply continuousLinearMap_isSelfAdjoint_of_inner_symm
  intro u v
  exact hDense.induction_on₂
    (isClosed_eq (by fun_prop) (by fun_prop))
    (fun x y => by
      rw [hIntertwine x, hIntertwine y]
      calc
        inner ℝ (J (S x)) (J y) = inner ℝ (S x) y := J.inner_map_map _ _
        _ = inner ℝ x (S y) := hS x y
        _ = inner ℝ (J x) (J (S y)) := (J.inner_map_map _ _).symm)
    u v

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedTransferSelfAdjointSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

@[reducible] local instance osBoundaryExcitationCompletedTransferSelfAdjointNormedAddCommGroup
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

/-- Expose the additive parent of the native tensor norm explicitly. -/
@[reducible] local instance osBoundaryExcitationCompletedTransferSelfAdjointAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    AddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  (osBoundaryExcitationCompletedTransferSelfAdjointNormedAddCommGroup
    H N hN beta hbeta).toAddCommGroup

@[reducible] local instance osBoundaryExcitationCompletedTransferSelfAdjointInnerProductSpace
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

local instance osBoundaryExcitationCompletedTransferSelfAdjointPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The physical one-slice normalized transfer restricted away from its full
top eigenspace satisfies the exact symmetry equation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x y : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta x) y =
      inner ℝ x
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta y) := by
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta (x :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (y : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      inner ℝ
        (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta (y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
  exact
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
      H N hN beta hbeta).isSymmetric _ _

/-- Every power of the physical one-slice excitation transfer satisfies the
same exact symmetry equation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ∀ x y : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta ^ n) x) y =
        inner ℝ x
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta ^ n) y) := by
  induction n with
  | zero =>
      intro x y
      simp
  | succ n ih =>
      intro x y
      calc
        inner ℝ
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ Nat.succ n) x) y =
          inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
                H N hN beta hbeta ^ n) x)) y := by
            rw [pow_succ']
            rfl
        _ = inner ℝ
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ n) x)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta y) :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
            H N hN beta hbeta _ _
        _ = inner ℝ x
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ n)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
                H N hN beta hbeta y)) := ih _ _
        _ = inner ℝ x
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
              H N hN beta hbeta ^ Nat.succ n) y) := by
            rw [pow_succ]
            rfl

/-- The native two-endpoint excitation transfer is symmetric for Mathlib's
native Hilbert tensor inner product.  Arbitrary tensors are expanded once as
finite sums of pure tensors, and symmetry is checked termwise. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_inner_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ∀ x y : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta n x) y =
        inner ℝ x
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta n y) := by
  intro x y
  obtain ⟨m, f, g, hx⟩ := TensorProduct.exists_sum_tmul_eq x
  obtain ⟨k, p, q, hy⟩ := TensorProduct.exists_sum_tmul_eq y
  rw [hx, hy]
  simp only [map_sum, inner_sum, sum_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_tmul]
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro i hi
  change
    inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta ^ n) (f i))
        (p j) *
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta ^ n) (g i))
        (q j) =
    inner ℝ (f i)
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta ^ n) (p j)) *
      inner ℝ (g i)
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta ^ n) (q j))
  exact congrArg₂ (fun a b : ℝ => a * b)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_symm
      H N hN beta hbeta n (f i) (p j))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_symm
      H N hN beta hbeta n (g i) (q j))

/-- The completed two-endpoint excitation transfer is self-adjoint.  Native
symmetry is transported along the dense algebraic isometry using the exact
completed-transfer intertwining receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) := by
  exact
    continuousLinearMap_isSelfAdjoint_of_dense_linearIsometry_intertwining
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_denseRange
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_inner_symm
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic
        H N hN beta hbeta n)

/-- The completed Wilson-boundary matrix elements inherit exact endpoint
symmetry from self-adjoint completed excitation dynamics. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n u v =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n v u := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner]
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta n
  have hT : IsSelfAdjoint T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
      H N hN beta hbeta n
  have hSymm : T.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hT
  change inner ℝ u (T v) = inner ℝ v (T u)
  calc
    inner ℝ u (T v) = inner ℝ (T u) v := (hSymm u v).symm
    _ = inner ℝ v (T u) := real_inner_comm _ _

/-- Audit-visible package for the completed finite-volume self-adjoint transfer
spine. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferSelfAdjointPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferSelfAdjoint :
    ∀ n : ℕ,
      IsSelfAdjoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)
  boundaryMatrixSymmetric :
    ∀ (n : ℕ)
      (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
          H N hN beta hbeta n u v =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
          H N hN beta hbeta n v u

/-- Construct the completed self-adjoint transfer package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedTransferSelfAdjointPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferSelfAdjointPackage
      H N hN beta hbeta :=
  { transferSelfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
        H N hN beta hbeta
    boundaryMatrixSymmetric :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_symm
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D