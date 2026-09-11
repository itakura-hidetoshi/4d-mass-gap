import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierCompletedOrthogonalDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairRestrictionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairRestrictionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairRestrictionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairRestrictionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairRestrictionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairRestrictionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairRestrictionSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The literal pair transfer normalized by the square of the physical one-slice
 top eigenvalue. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2)⁻¹ •
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta

private theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sq_ne_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2 ≠ 0 := by
  exact pow_ne_zero 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta).ne'

/-- The normalized pair transfer fixes every decomposable vector in the full
 top-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
          H N hN beta hbeta u v) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
        H N hN beta hbeta u v := by
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  have hc : c ≠ 0 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sq_ne_zero
        H N hN beta hbeta
  change
    c⁻¹ • periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
      (realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta v)) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_top_top]
  change
    c⁻¹ • c • realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta u)
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta v) =
    realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta u)
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta v)
  simp [hc]

/-- The normalized pair transfer acts on `K ⊠ F` by the one-slice orthogonal
 restriction on the excitation factor. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_top
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
          H N hN beta hbeta f u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f) u := by
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  have hc : c ≠ 0 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sq_ne_zero
        H N hN beta hbeta
  change
    c⁻¹ • periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
      (realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u)) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_orthogonal_top]
  change
    c⁻¹ • c • realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta u) =
    realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta u)
  simp [hc]

/-- The normalized pair transfer acts on `F ⊠ K` by the one-slice orthogonal
 restriction on the excitation factor. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
      H N hN beta hbeta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
          H N hN beta hbeta u f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
        H N hN beta hbeta u
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f) := by
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  have hc : c ≠ 0 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sq_ne_zero
        H N hN beta hbeta
  change
    c⁻¹ • periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
      (realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
          H N hN beta hbeta u)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_top_orthogonal]
  change
    c⁻¹ • c • realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta u)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f)) =
    realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceL2LinearIsometry
        H N hN beta hbeta u)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f))
  simp [hc]

/-- The normalized pair transfer acts on `K ⊠ K` by the tensor square of the
 one-slice orthogonal restriction. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_orthogonal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
          H N hN beta hbeta f g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta g) := by
  let c : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ ^ 2
  have hc : c ≠ 0 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sq_ne_zero
        H N hN beta hbeta
  change
    c⁻¹ • periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
      (realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta g)) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_orthogonal_orthogonal]
  change
    c⁻¹ • c • realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta g)) =
    realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta g))
  simp [hc]

section Invariance

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "TTspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan H N hN beta hbeta
local notation "OTspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan H N hN beta hbeta
local notation "TOspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan H N hN beta hbeta
local notation "OOspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan H N hN beta hbeta
local notation "Nspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan H N hN beta hbeta
local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure H N hN beta hbeta
local notation "OT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockClosure H N hN beta hbeta
local notation "TO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockClosure H N hN beta hbeta
local notation "OO" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "PP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

private theorem continuousLinearMap_topologicalClosure_invariant
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (V : Submodule ℝ E)
    (hV : V ≤ (V).comap A.toLinearMap) :
    V.topologicalClosure ≤ (V.topologicalClosure).comap A.toLinearMap := by
  apply V.topologicalClosure_minimal
  · intro x hx
    change A x ∈ V.topologicalClosure
    exact V.le_topologicalClosure (hV hx)
  · change IsClosed (A ⁻¹' (V.topologicalClosure : Set E))
    exact (Submodule.isClosed_topologicalClosure V).preimage A.continuous

/-- The algebraic top-top block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_normalizedTransfer_invariant :
    TTspan ≤ (TTspan).comap (S₂).toLinearMap := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan]
  refine Submodule.span_le.2 ?_
  rintro z ⟨⟨u, v⟩, rfl⟩
  change S₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
        H N hN beta hbeta u v) ∈
    Submodule.span ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopGeneratorSet
        H N hN beta hbeta)
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_top]
  apply Submodule.subset_span
  exact ⟨(u, v), rfl⟩

/-- The algebraic `K ⊠ F` block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_invariant :
    OTspan ≤ (OTspan).comap (S₂).toLinearMap := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan]
  refine Submodule.span_le.2 ?_
  rintro z ⟨⟨f, u⟩, rfl⟩
  change S₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopDecomposableL2
        H N hN beta hbeta f u) ∈
    Submodule.span ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopGeneratorSet
        H N hN beta hbeta)
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_top]
  apply Submodule.subset_span
  exact
    ⟨(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta f, u), rfl⟩

/-- The algebraic `F ⊠ K` block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_invariant :
    TOspan ≤ (TOspan).comap (S₂).toLinearMap := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan]
  refine Submodule.span_le.2 ?_
  rintro z ⟨⟨u, f⟩, rfl⟩
  change S₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalDecomposableL2
        H N hN beta hbeta u f) ∈
    Submodule.span ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalGeneratorSet
        H N hN beta hbeta)
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_top_orthogonal]
  apply Submodule.subset_span
  exact
    ⟨(u, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta f), rfl⟩

/-- The algebraic `K ⊠ K` block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_invariant :
    OOspan ≤ (OOspan).comap (S₂).toLinearMap := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan]
  refine Submodule.span_le.2 ?_
  rintro z ⟨⟨f, g⟩, rfl⟩
  change S₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
        H N hN beta hbeta f g) ∈
    Submodule.span ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalGeneratorSet
        H N hN beta hbeta)
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_orthogonal_orthogonal]
  apply Submodule.subset_span
  exact
    ⟨(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta g), rfl⟩

/-- The algebraic sum of all three non-top blocks is invariant under normalized
 pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan_normalizedTransfer_invariant :
    Nspan ≤ (Nspan).comap (S₂).toLinearMap := by
  intro x hx
  change S₂ x ∈ Nspan
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan] at hx ⊢
  rcases Submodule.mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
  rcases Submodule.mem_sup.1 hy with ⟨a, ha, b, hb, rfl⟩
  rw [map_add, map_add]
  have ha' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta ha
  have hb' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta hb
  have hz' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta hz
  refine Submodule.mem_sup.2 ?_
  refine ⟨S₂ a + S₂ b, ?_, S₂ z, hz', rfl⟩
  exact Submodule.mem_sup.2 ⟨S₂ a, ha', S₂ b, hb', rfl⟩

/-- The completed top-top block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_invariant :
    TT ≤ (TT).comap (S₂).toLinearMap := by
  change
    (TTspan).topologicalClosure ≤
      ((TTspan).topologicalClosure).comap (S₂).toLinearMap
  exact continuousLinearMap_topologicalClosure_invariant S₂ TTspan
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- The completed `K ⊠ F` block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockClosure_normalizedTransfer_invariant :
    OT ≤ (OT).comap (S₂).toLinearMap := by
  change
    (OTspan).topologicalClosure ≤
      ((OTspan).topologicalClosure).comap (S₂).toLinearMap
  exact continuousLinearMap_topologicalClosure_invariant S₂ OTspan
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- The completed `F ⊠ K` block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockClosure_normalizedTransfer_invariant :
    TO ≤ (TO).comap (S₂).toLinearMap := by
  change
    (TOspan).topologicalClosure ≤
      ((TOspan).topologicalClosure).comap (S₂).toLinearMap
  exact continuousLinearMap_topologicalClosure_invariant S₂ TOspan
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- The completed `K ⊠ K` block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure_normalizedTransfer_invariant :
    OO ≤ (OO).comap (S₂).toLinearMap := by
  change
    (OOspan).topologicalClosure ≤
      ((OOspan).topologicalClosure).comap (S₂).toLinearMap
  exact continuousLinearMap_topologicalClosure_invariant S₂ OOspan
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- The completed non-top block is invariant under normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_invariant :
    NN ≤ (NN).comap (S₂).toLinearMap := by
  change
    (Nspan).topologicalClosure ≤
      ((Nspan).topologicalClosure).comap (S₂).toLinearMap
  exact continuousLinearMap_topologicalClosure_invariant S₂ Nspan
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- The completed physical pair carrier is invariant under normalized pair
 transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant :
    PP ≤ (PP).comap (S₂).toLinearMap := by
  intro x hx
  change S₂ x ∈ PP
  have hx' : x ∈ TT ⊔ NN := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_topTopClosure_sup_nonTopClosure
      H N hN beta hbeta]
    exact hx
  rcases Submodule.mem_sup.1 hx' with ⟨t, ht, n, hn, hsum⟩
  rw [← hsum, map_add]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_topTopClosure_sup_nonTopClosure
    H N hN beta hbeta]
  refine Submodule.mem_sup.2 ?_
  exact
    ⟨S₂ t,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta ht,
      S₂ n,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta hn,
      rfl⟩

private noncomputable def continuousLinearMapRestrictionOfInvariant
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (V : Submodule ℝ E)
    (hV : V ≤ (V).comap A.toLinearMap) :
    V →L[ℝ] V := by
  let L : V →ₗ[ℝ] V :=
    { toFun := fun x => ⟨A (x : E), hV x.property⟩
      map_add' := by
        intro x y
        ext
        exact A.map_add (x : E) (y : E)
      map_smul' := by
        intro c x
        ext
        exact A.map_smul c (x : E) }
  exact L.mkContinuous ‖A‖ fun x => by
    change ‖A (x : E)‖ ≤ ‖A‖ * ‖(x : E)‖
    exact A.le_opNorm (x : E)

/-- Normalized pair transfer restricted to the completed top-top block. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockTransferOperator :
    TT →L[ℝ] TT :=
  continuousLinearMapRestrictionOfInvariant S₂ TT
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- Normalized pair transfer restricted to the completed `K ⊠ F` block. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockTransferOperator :
    OT →L[ℝ] OT :=
  continuousLinearMapRestrictionOfInvariant S₂ OT
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockClosure_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- Normalized pair transfer restricted to the completed `F ⊠ K` block. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockTransferOperator :
    TO →L[ℝ] TO :=
  continuousLinearMapRestrictionOfInvariant S₂ TO
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockClosure_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- Normalized pair transfer restricted to the completed `K ⊠ K` block. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockTransferOperator :
    OO →L[ℝ] OO :=
  continuousLinearMapRestrictionOfInvariant S₂ OO
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure_normalizedTransfer_invariant
      H N hN beta hbeta)

/-- Normalized pair transfer restricted to the entire completed non-top physical
 pair sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator :
    NN →L[ℝ] NN :=
  continuousLinearMapRestrictionOfInvariant S₂ NN
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_invariant
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockTransferOperator_coe_apply
    (x : TT) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockTransferOperator
        H N hN beta hbeta x : TT) : PairE) = S₂ (x : PairE) := rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockTransferOperator_coe_apply
    (x : OT) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockTransferOperator
        H N hN beta hbeta x : OT) : PairE) = S₂ (x : PairE) := rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockTransferOperator_coe_apply
    (x : TO) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockTransferOperator
        H N hN beta hbeta x : TO) : PairE) = S₂ (x : PairE) := rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockTransferOperator_coe_apply
    (x : OO) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockTransferOperator
        H N hN beta hbeta x : OO) : PairE) = S₂ (x : PairE) := rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_coe_apply
    (x : NN) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator
        H N hN beta hbeta x : NN) : PairE) = S₂ (x : PairE) := rfl

/-- Audit-visible receipt that normalized pair transfer is a genuine closed-sector
 dynamical operator. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedBlockTransferRestrictionPackage :
    Prop where
  topTopInvariant : TT ≤ (TT).comap (S₂).toLinearMap
  orthogonalTopInvariant : OT ≤ (OT).comap (S₂).toLinearMap
  topOrthogonalInvariant : TO ≤ (TO).comap (S₂).toLinearMap
  orthogonalOrthogonalInvariant : OO ≤ (OO).comap (S₂).toLinearMap
  nonTopInvariant : NN ≤ (NN).comap (S₂).toLinearMap
  physicalCarrierInvariant : PP ≤ (PP).comap (S₂).toLinearMap

/-- Construct the completed block-transfer restriction package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedBlockTransferRestrictionPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedBlockTransferRestrictionPackage
      H N hN beta hbeta :=
  { topTopInvariant :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta
    orthogonalTopInvariant :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta
    topOrthogonalInvariant :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta
    orthogonalOrthogonalInvariant :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta
    nonTopInvariant :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_invariant
        H N hN beta hbeta
    physicalCarrierInvariant :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
        H N hN beta hbeta }

end Invariance

end

end MathlibAnalytic
end MGAP4D
