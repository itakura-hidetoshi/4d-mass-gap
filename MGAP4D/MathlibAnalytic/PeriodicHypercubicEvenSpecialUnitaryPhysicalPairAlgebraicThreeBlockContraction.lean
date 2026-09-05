import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedBlockTransferRestriction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativePairIsometry
import MGAP4D.MathlibAnalytic.HilbertTensorLinearIsometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairAlgebraicContractionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairAlgebraicContractionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairAlgebraicContractionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairAlgebraicContractionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairAlgebraicContractionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairAlgebraicContractionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairAlgebraicContractionSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Native algebraic Hilbert tensor core for the mixed block `K ⊠ F`. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Type :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta ⊗[ℝ]
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta

/-- Native algebraic Hilbert tensor core for the mixed block `F ⊠ K`. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Type :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta ⊗[ℝ]
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta

@[reducible] local instance physicalPairOrthogonalTopTensorNormedAddCommGroup
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)

@[reducible] local instance physicalPairOrthogonalTopTensorInnerProductSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)

@[reducible] local instance physicalPairTopOrthogonalTensorNormedAddCommGroup
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

@[reducible] local instance physicalPairTopOrthogonalTensorInnerProductSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

@[reducible] local instance physicalPairOrthogonalOrthogonalTensorNormedAddCommGroup
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

@[reducible] local instance physicalPairOrthogonalOrthogonalTensorInnerProductSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

@[reducible] local instance physicalPairAlgebraicContractionL2TensorNormedAddCommGroup
    (H N : ℕ) :
    NormedAddCommGroup
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (F := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

@[reducible] local instance physicalPairAlgebraicContractionL2TensorInnerProductSpace
    (H N : ℕ) :
    InnerProductSpace ℝ
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (F := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Tensor the one-slice `K` and `F` inclusions before passing to pair `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorFactorLinearIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  hilbertTensorLinearIsometry
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (G := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (H := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta)

/-- Tensor the one-slice `F` and `K` inclusions before passing to pair `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorFactorLinearIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  hilbertTensorLinearIsometry
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (F := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (G := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (H := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorFactorLinearIsometry_tmul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorFactorLinearIsometry
        H N hN beta hbeta (f ⊗ₜ[ℝ] u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f ⊗ₜ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u := by
  rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorFactorLinearIsometry_tmul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorFactorLinearIsometry
        H N hN beta hbeta (u ⊗ₜ[ℝ] f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u ⊗ₜ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f := by
  rfl

/-- Exact native-Hilbert isometry from `K ⊠ F` algebraic tensors into pair `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftLinearIsometry
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorFactorLinearIsometry
      H N hN beta hbeta)

/-- Exact native-Hilbert isometry from `F ⊠ K` algebraic tensors into pair `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftLinearIsometry
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorFactorLinearIsometry
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry_tmul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
        H N hN beta hbeta (f ⊗ₜ[ℝ] u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
        H N hN beta hbeta f u := by
  change
    realL2ExternalTensorLift
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorFactorLinearIsometry
          H N hN beta hbeta (f ⊗ₜ[ℝ] u)) = _
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorFactorLinearIsometry_tmul]
  rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry_tmul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
        H N hN beta hbeta (u ⊗ₜ[ℝ] f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
        H N hN beta hbeta u f := by
  change
    realL2ExternalTensorLift
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorFactorLinearIsometry
          H N hN beta hbeta (u ⊗ₜ[ℝ] f)) = _
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorFactorLinearIsometry_tmul]
  rfl

/-- The algebraic `K ⊠ F` block span is exactly the range of its native tensor isometry. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_eq_range_nativeTensorIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan
        H N hN beta hbeta =
      LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
          H N hN beta hbeta).toLinearMap := by
  apply le_antisymm
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan]
    refine Submodule.span_le.2 ?_
    rintro z ⟨⟨f, u⟩, rfl⟩
    refine ⟨f ⊗ₜ[ℝ] u, ?_⟩
    exact periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry_tmul
      H N hN beta hbeta f u
  · rintro z ⟨x, rfl⟩
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
          H N hN beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan
          H N hN beta hbeta
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f u =>
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry_tmul]
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan]
        apply Submodule.subset_span
        exact ⟨(f, u), rfl⟩
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy

/-- The algebraic `F ⊠ K` block span is exactly the range of its native tensor isometry. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_eq_range_nativeTensorIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan
        H N hN beta hbeta =
      LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
          H N hN beta hbeta).toLinearMap := by
  apply le_antisymm
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan]
    refine Submodule.span_le.2 ?_
    rintro z ⟨⟨u, f⟩, rfl⟩
    refine ⟨u ⊗ₜ[ℝ] f, ?_⟩
    exact periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry_tmul
      H N hN beta hbeta u f
  · rintro z ⟨x, rfl⟩
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
          H N hN beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan
          H N hN beta hbeta
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u f =>
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry_tmul]
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan]
        apply Submodule.subset_span
        exact ⟨(u, f), rfl⟩
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy

/-- The algebraic `K ⊠ K` block span is exactly the range of the existing native tensor isometry. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_eq_range_nativeTensorIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan
        H N hN beta hbeta =
      LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
          H N hN beta hbeta).toLinearMap := by
  apply le_antisymm
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan]
    refine Submodule.span_le.2 ?_
    rintro z ⟨⟨f, g⟩, rfl⟩
    refine ⟨f ⊗ₜ[ℝ] g, ?_⟩
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
          H N hN beta hbeta (f ⊗ₜ[ℝ] g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
          H N hN beta hbeta f g
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry_apply]
    exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul
      H N hN beta hbeta f g
  · rintro z ⟨x, rfl⟩
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
          H N hN beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan
          H N hN beta hbeta
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry_apply]
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul]
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan]
        apply Submodule.subset_span
        exact ⟨(f, g), rfl⟩
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy

section Dynamics

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "Ftop" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "JOT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
    H N hN beta hbeta
local notation "JTO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
    H N hN beta hbeta
local notation "JOO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
    H N hN beta hbeta

/-- Native `R ⊗ I` action on the whole algebraic `K ⊠ F` tensor core. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensorTransferOperator :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta :=
  hilbertTensorRTensor
    (E := K) (F := K) (G := Ftop)
    R Ftop

/-- Native `I ⊗ R` action on the whole algebraic `F ⊠ K` tensor core. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensorTransferOperator :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta :=
  hilbertTensorLTensor
    (E := Ftop) (G := K) (H := K)
    R Ftop

/-- On the whole algebraic `K ⊠ F` tensor core, normalized pair transfer is exactly `R ⊗ I`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensor_intertwines_normalizedTransfer
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
      H N hN beta hbeta) :
    S₂ (JOT x) =
      JOT
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensorTransferOperator
          H N hN beta hbeta x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f u =>
      simp only [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensorTransferOperator,
        hilbertTensorRTensor_tmul,
        periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry_tmul]
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_top
          H N hN beta hbeta f u
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- On the whole algebraic `F ⊠ K` tensor core, normalized pair transfer is exactly `I ⊗ R`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensor_intertwines_normalizedTransfer
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
      H N hN beta hbeta) :
    S₂ (JTO x) =
      JTO
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensorTransferOperator
          H N hN beta hbeta x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u f =>
      simp only [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensorTransferOperator,
        hilbertTensorLTensor_tmul,
        periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry_tmul]
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_orthogonal
          H N hN beta hbeta u f
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- On the whole algebraic `K ⊠ K` tensor core, normalized pair transfer is the existing tensor-square transfer at one step. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalNativeTensor_intertwines_normalizedTransfer
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    S₂ (JOO x) =
      JOO
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta 1 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      change
        S₂
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
              H N hN beta hbeta f g) =
          periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
            H N hN beta hbeta (R f) (R g)
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_orthogonal
          H N hN beta hbeta f g
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Every vector in the algebraic `K ⊠ F` block obeys the one-factor operator bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_norm_le
    (x : PairE)
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan
      H N hN beta hbeta) :
    ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ := by
  have hxRange :
      x ∈ LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
          H N hN beta hbeta).toLinearMap := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_eq_range_nativeTensorIsometry
      H N hN beta hbeta]
    exact hx
  rcases hxRange with ⟨y, rfl⟩
  change ‖S₂ (JOT y)‖ ≤ ‖R‖ * ‖JOT y‖
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensor_intertwines_normalizedTransfer]
  rw [(JOT).norm_map, (JOT).norm_map]
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensorTransferOperator
        H N hN beta hbeta y‖ ≤ ‖R‖ * ‖y‖
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensorTransferOperator
  exact hilbertTensorRTensor_bound
    (E := K) (F := K) (G := Ftop) R y

/-- Every vector in the algebraic `F ⊠ K` block obeys the one-factor operator bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_norm_le
    (x : PairE)
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan
      H N hN beta hbeta) :
    ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ := by
  have hxRange :
      x ∈ LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
          H N hN beta hbeta).toLinearMap := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_eq_range_nativeTensorIsometry
      H N hN beta hbeta]
    exact hx
  rcases hxRange with ⟨y, rfl⟩
  change ‖S₂ (JTO y)‖ ≤ ‖R‖ * ‖JTO y‖
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensor_intertwines_normalizedTransfer]
  rw [(JTO).norm_map, (JTO).norm_map]
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensorTransferOperator
        H N hN beta hbeta y‖ ≤ ‖R‖ * ‖y‖
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensorTransferOperator
  calc
    ‖hilbertTensorLTensor (E := Ftop) (G := K) (H := K) R Ftop y‖ ≤
        ‖hilbertTensorLTensor (E := Ftop) (G := K) (H := K) R Ftop‖ * ‖y‖ :=
      (hilbertTensorLTensor (E := Ftop) (G := K) (H := K) R Ftop).le_opNorm y
    _ ≤ ‖R‖ * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        (hilbertTensorLTensor_norm_le (E := Ftop) (G := K) (H := K) R)
        (norm_nonneg y)

/-- Every vector in the algebraic `K ⊠ K` block obeys the two-factor operator bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_norm_le
    (x : PairE)
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan
      H N hN beta hbeta) :
    ‖S₂ x‖ ≤ (‖R‖ * ‖R‖) * ‖x‖ := by
  have hxRange :
      x ∈ LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
          H N hN beta hbeta).toLinearMap := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_eq_range_nativeTensorIsometry
      H N hN beta hbeta]
    exact hx
  rcases hxRange with ⟨y, rfl⟩
  change ‖S₂ (JOO y)‖ ≤ (‖R‖ * ‖R‖) * ‖JOO y‖
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalNativeTensor_intertwines_normalizedTransfer]
  rw [(JOO).norm_map, (JOO).norm_map]
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
      H N hN beta hbeta 1
  have hT : ‖T‖ ≤ ‖R‖ * ‖R‖ := by
    simpa [T, pow_one] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_mul
        H N hN beta hbeta 1
  calc
    ‖T y‖ ≤ ‖T‖ * ‖y‖ := T.le_opNorm y
    _ ≤ (‖R‖ * ‖R‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg y)

/-- Audit-visible algebraic three-block contraction package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicThreeBlockContractionPackage :
    Prop where
  orthogonalTop :
    ∀ x : PairE,
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan
          H N hN beta hbeta →
        ‖S₂ x‖ ≤ ‖R‖ * ‖x‖
  topOrthogonal :
    ∀ x : PairE,
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan
          H N hN beta hbeta →
        ‖S₂ x‖ ≤ ‖R‖ * ‖x‖
  orthogonalOrthogonal :
    ∀ x : PairE,
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan
          H N hN beta hbeta →
        ‖S₂ x‖ ≤ (‖R‖ * ‖R‖) * ‖x‖

/-- Construct the algebraic three-block contraction package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicThreeBlockContractionPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicThreeBlockContractionPackage
      H N hN beta hbeta :=
  { orthogonalTop :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_norm_le
        H N hN beta hbeta
    topOrthogonal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_norm_le
        H N hN beta hbeta
    orthogonalOrthogonal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_norm_le
        H N hN beta hbeta }

end Dynamics

end

end MathlibAnalytic
end MGAP4D
