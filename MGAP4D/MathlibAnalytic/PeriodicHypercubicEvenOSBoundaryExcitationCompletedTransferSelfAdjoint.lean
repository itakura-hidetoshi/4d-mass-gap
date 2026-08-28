import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedBoundaryMatrixElement
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open UniformSpace
open scoped TensorProduct InnerProductSpace InnerProduct

noncomputable section

/-- Tensoring two bounded real-Hilbert endomorphisms that are symmetric at the
level of inner products again gives an inner-product symmetric endomorphism. -/
theorem hilbertTensorMap_inner_symm
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (A : E →L[ℝ] E)
    (B : F →L[ℝ] F)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) :
    ∀ x y : E ⊗[ℝ] F,
      inner ℝ (hilbertTensorMap A B x) y =
        inner ℝ x (hilbertTensorMap A B y) := by
  intro x y
  induction x using TensorProduct.induction_on with
  | zero =>
      simpa only [map_zero, inner_zero_left]
  | tmul x₁ x₂ =>
      induction y using TensorProduct.induction_on with
      | zero =>
          simpa only [map_zero, inner_zero_right]
      | tmul y₁ y₂ =>
          change
            inner ℝ (A x₁ ⊗ₜ[ℝ] B x₂) (y₁ ⊗ₜ[ℝ] y₂) =
              inner ℝ (x₁ ⊗ₜ[ℝ] x₂) (A y₁ ⊗ₜ[ℝ] B y₂)
          rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul,
            hA x₁ y₁, hB x₂ y₂]
      | add y z hy hz =>
          simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz =>
      simp only [map_add, inner_add_left, hx, hz]

/-- Inner-product symmetry of a bounded real-Hilbert endomorphism is inherited
by every composition power. -/
theorem continuousLinearMap_pow_inner_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (n : ℕ) :
    ∀ x y : E,
      inner ℝ ((A ^ n) x) y = inner ℝ x ((A ^ n) y) := by
  have hSymm : (A : E →ₗ[ℝ] E).IsSymmetric := hA
  exact hSymm.pow n

/-- Inner-product symmetry survives Mathlib's native completion functor. -/
theorem continuousLinearMap_completion_inner_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) :
    ∀ x y : UniformSpace.Completion E,
      inner ℝ (A.completion x) y = inner ℝ x (A.completion y) := by
  intro x y
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro a
    refine UniformSpace.Completion.induction_on y ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro b
      simpa using hA a b

/-- Isometric conjugation preserves inner-product symmetry. -/
theorem continuousLinearMapConjugateLinearIsometryEquiv_inner_symm
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F)
    (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) :
    ∀ x y : F,
      inner ℝ (continuousLinearMapConjugateLinearIsometryEquiv U A x) y =
        inner ℝ x (continuousLinearMapConjugateLinearIsometryEquiv U A y) := by
  intro x y
  change
    inner ℝ (U (A (U.symm x))) y =
      inner ℝ x (U (A (U.symm y)))
  calc
    inner ℝ (U (A (U.symm x))) y =
        inner ℝ (A (U.symm x)) (U.symm y) := by
      simpa using U.inner_map_map (A (U.symm x)) (U.symm y)
    _ = inner ℝ (U.symm x) (A (U.symm y)) := hA _ _
    _ = inner ℝ x (U (A (U.symm y))) := by
      simpa using (U.inner_map_map (U.symm x) (A (U.symm y))).symm

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
            H N hN beta hbeta ^ n) y) :=
  continuousLinearMap_pow_inner_symm
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
      H N hN beta hbeta)
    n

/-- Every native algebraic two-endpoint excitation transfer satisfies the exact
Hilbert-tensor symmetry equation. -/
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
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_map]
  exact
    hilbertTensorMap_inner_symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta ^ n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta ^ n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_symm
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_symm
        H N hN beta hbeta n)

/-- The native two-endpoint symmetry equation survives Hilbert completion. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_inner_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ∀ x y : UniformSpace.Completion
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta),
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
            H N hN beta hbeta n x) y =
        inner ℝ x
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
            H N hN beta hbeta n y) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
  exact
    continuousLinearMap_completion_inner_symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_inner_symm
        H N hN beta hbeta n)

/-- The actual bounded transfer on the concrete completed pair-Hilbert
excitation sector satisfies the exact symmetry equation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ∀ x y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n x) y =
        inner ℝ x
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n y) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_inner_symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_inner_symm
        H N hN beta hbeta n)

/-- On the complete pair-Hilbert excitation sector, the exact symmetry equation
upgrades to Mathlib self-adjointness. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) :=
  continuousLinearMap_isSelfAdjoint_of_inner_symm
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_symm
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
  calc
    inner ℝ u
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n v) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n u) v :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_symm
        H N hN beta hbeta n u v).symm
    _ = inner ℝ v
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n u) := real_inner_comm _ _

/-- Audit-visible package for the completed finite-volume self-adjoint transfer
spine. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferSelfAdjointPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferInnerSymmetric :
    ∀ (n : ℕ)
      (x y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n x) y =
        inner ℝ x
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n y)
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
  { transferInnerSymmetric :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_symm
        H N hN beta hbeta
    transferSelfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
        H N hN beta hbeta
    boundaryMatrixSymmetric :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_symm
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
