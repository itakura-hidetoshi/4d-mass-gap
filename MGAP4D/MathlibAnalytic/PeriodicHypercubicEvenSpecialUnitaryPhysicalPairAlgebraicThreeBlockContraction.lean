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

/-- Exact native-Hilbert isometry from `K ⊠ F` algebraic tensors into pair `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorLinearIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftLinearIsometry
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (hilbertTensorLinearIsometry
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta))

/-- Exact native-Hilbert isometry from `F ⊠ K` algebraic tensors into pair `L²`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorLinearIsometry
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftLinearIsometry
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (hilbertTensorLinearIsometry
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta))

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
    intro z hz
    rcases hz with ⟨⟨f, u⟩, rfl⟩
    exact ⟨f ⊗ₜ[ℝ] u, rfl⟩
  · rintro z ⟨x, rfl⟩
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
    intro z hz
    rcases hz with ⟨⟨u, f⟩, rfl⟩
    exact ⟨u ⊗ₜ[ℝ] f, rfl⟩
  · rintro z ⟨x, rfl⟩
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

/-- The algebraic `K ⊠ K` block span is exactly the range of the pre-existing
native excitation-tensor isometry. -/
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
    intro z hz
    rcases hz with ⟨⟨f, g⟩, rfl⟩
    exact ⟨f ⊗ₜ[ℝ] g, rfl⟩
  · rintro z ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
        change
          periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
              H N hN beta hbeta f g ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan
              H N hN beta hbeta
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
local notation "F" =>
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

/-- On the whole algebraic `K ⊠ F` tensor core, normalized pair transfer is
exactly `R ⊗ I`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensor_intertwines_normalizedTransfer
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopAlgebraicTensorCore
      H N hN beta hbeta) :
    S₂ (JOT x) = JOT (hilbertTensorRTensor R F x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f u =>
      change
        S₂
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
              H N hN beta hbeta f u) =
          periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
            H N hN beta hbeta (R f) u
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_top
          H N hN beta hbeta f u
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]

/-- On the whole algebraic `F ⊠ K` tensor core, normalized pair transfer is
exactly `I ⊗ R`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensor_intertwines_normalizedTransfer
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalAlgebraicTensorCore
      H N hN beta hbeta) :
    S₂ (JTO x) = JTO (hilbertTensorLTensor R F x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u f =>
      change
        S₂
            (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
              H N hN beta hbeta u f) =
          periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
            H N hN beta hbeta u (R f)
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_orthogonal
          H N hN beta hbeta u f
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]

/-- On the whole algebraic `K ⊠ K` tensor core, normalized pair transfer is
exactly the native tensor-square transfer at one time step. -/
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
      rw [map_add, map_add, map_add, hx, hy]

/-- Every vector in the algebraic `K ⊠ F` block obeys the sharp one-factor
operator bound `‖S₂ x‖ ≤ ‖R‖ ‖x‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_norm_le
    (x : PairE)
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan
      H N hN beta hbeta) :
    ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ := by
  have hxRange : x ∈ LinearMap.range JOT.toLinearMap := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_eq_range_nativeTensorIsometry
      H N hN beta hbeta]
    exact hx
  rcases hxRange with ⟨y, rfl⟩
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopNativeTensor_intertwines_normalizedTransfer]
  rw [JOT.norm_map, JOT.norm_map]
  exact hilbertTensorRTensor_bound R y

/-- Every vector in the algebraic `F ⊠ K` block obeys the sharp one-factor
operator bound `‖S₂ x‖ ≤ ‖R‖ ‖x‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_norm_le
    (x : PairE)
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan
      H N hN beta hbeta) :
    ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ := by
  have hxRange : x ∈ LinearMap.range JTO.toLinearMap := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_eq_range_nativeTensorIsometry
      H N hN beta hbeta]
    exact hx
  rcases hxRange with ⟨y, rfl⟩
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalNativeTensor_intertwines_normalizedTransfer]
  rw [JTO.norm_map, JTO.norm_map]
  exact hilbertTensorLTensor_norm_le R |>.trans
    (by
      have h := (hilbertTensorLTensor R F).le_opNorm y
      exact le_trans h
        (mul_le_mul_of_nonneg_right
          (hilbertTensorLTensor_norm_le (E := F) R) (norm_nonneg y)))

/-- Every vector in the algebraic `K ⊠ K` block obeys the two-factor operator
bound `‖S₂ x‖ ≤ ‖R‖² ‖x‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_norm_le
    (x : PairE)
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan
      H N hN beta hbeta) :
    ‖S₂ x‖ ≤ (‖R‖ * ‖R‖) * ‖x‖ := by
  have hxRange : x ∈ LinearMap.range JOO.toLinearMap := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_eq_range_nativeTensorIsometry
      H N hN beta hbeta]
    exact hx
  rcases hxRange with ⟨y, rfl⟩
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
      H N hN beta hbeta 1
  have hT : ‖T‖ ≤ ‖R‖ * ‖R‖ := by
    simpa [T] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_norm_le_mul
        H N hN beta hbeta 1
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalNativeTensor_intertwines_normalizedTransfer]
  rw [JOO.norm_map, JOO.norm_map]
  calc
    ‖T y‖ ≤ ‖T‖ * ‖y‖ := T.le_opNorm y
    _ ≤ (‖R‖ * ‖R‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg y)

/-- Audit-visible algebraic three-block contraction package.  It is entirely
finite-volume and makes no scale-uniform or continuum claim. -/
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
