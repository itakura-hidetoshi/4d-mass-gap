import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedRealEigenvalueExclusion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open UniformSpace
open scoped TensorProduct InnerProductSpace InnerProduct

noncomputable section

/-- Tensoring two symmetric bounded real-Hilbert endomorphisms gives a
symmetric endomorphism for Mathlib's native Hilbert tensor inner product. -/
theorem hilbertTensorMap_isSymmetric
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (A : E →L[ℝ] E)
    (B : F →L[ℝ] F)
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric)
    (hB : (B : F →ₗ[ℝ] F).IsSymmetric) :
    ((hilbertTensorMap
        (E := E) (F := E) (G := F) (H := F) A B :
        (E ⊗[ℝ] F) →L[ℝ] (E ⊗[ℝ] F)) :
      (E ⊗[ℝ] F) →ₗ[ℝ] (E ⊗[ℝ] F)).IsSymmetric := by
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul y₁ y₂ =>
          simp only [hilbertTensorMap_tmul, TensorProduct.inner_tmul]
          rw [hA x₁ y₁, hB x₂ y₂]
      | add y z hy hz =>
          simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz =>
      simp only [map_add, inner_add_left, hx, hz]

/-- Symmetry of a bounded real-Hilbert endomorphism survives Mathlib's native
completion functor.  The proof uses the canonical dense copy twice and closes
by continuity of the two inner-product expressions. -/
theorem continuousLinearMap_completion_isSymmetric
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric) :
    ((A.completion : UniformSpace.Completion E →L[ℝ]
        UniformSpace.Completion E) :
      UniformSpace.Completion E →ₗ[ℝ]
        UniformSpace.Completion E).IsSymmetric := by
  intro x y
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro a
    refine UniformSpace.Completion.induction_on y ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro b
      simpa using hA a b

/-- Isometric conjugation preserves symmetry. -/
theorem continuousLinearMapConjugateLinearIsometryEquiv_isSymmetric
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F)
    (A : E →L[ℝ] E)
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric) :
    ((continuousLinearMapConjugateLinearIsometryEquiv U A : F →L[ℝ] F) :
      F →ₗ[ℝ] F).IsSymmetric := by
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

/-- Powers of a symmetric bounded endomorphism remain symmetric, with the
continuous-linear-map coercion exposed explicitly. -/
theorem continuousLinearMap_pow_isSymmetric
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (hA : (A : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ) :
    (((A ^ n : E →L[ℝ] E) : E →ₗ[ℝ] E)).IsSymmetric := by
  simpa using hA.pow n

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
top eigenspace is symmetric. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta).IsSymmetric := by
  have hPos :=
    realHilbertTopEigenspaceOrthogonalRestriction_isPositive
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta)
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator]
    using hPos.isSymmetric

/-- Every native algebraic two-endpoint excitation transfer is symmetric. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta).IsSymmetric := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_map]
  apply hilbertTensorMap_isSymmetric
  all_goals
    apply continuousLinearMap_pow_isSymmetric
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isSymmetric
        H N hN beta hbeta

/-- The symmetric native tensor transfer remains symmetric after Hilbert
completion. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n :
      UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta) →L[ℝ]
        UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta)) :
      UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta) →ₗ[ℝ]
        UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta)).IsSymmetric := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
  exact
    continuousLinearMap_completion_isSymmetric
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_isSymmetric
        H N hN beta hbeta n)

/-- The actual bounded transfer on the concrete completed pair-Hilbert
excitation sector is symmetric. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta).IsSymmetric := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_isSymmetric
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_isSymmetric
        H N hN beta hbeta n)

/-- On the complete pair-Hilbert excitation sector, bounded symmetry is exact
self-adjointness in Mathlib's adjoint sense. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSymmetric
      H N hN beta hbeta n).clm_adjoint_eq

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
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSymmetric
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
  transferSymmetric :
    ∀ n : ℕ,
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta →L[ℝ]
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta) :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta →ₗ[ℝ]
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta).IsSymmetric
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
  { transferSymmetric :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSymmetric
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
