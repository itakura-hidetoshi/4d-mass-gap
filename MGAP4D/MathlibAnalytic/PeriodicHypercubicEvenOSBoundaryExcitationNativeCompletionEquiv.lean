import MGAP4D.MathlibAnalytic.DenseLinearIsometryCompletionEquiv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativePairIsometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open Set Function Topology
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance osBoundaryExcitationNativeCompletionEquivSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationNativeCompletionEquivSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationNativeCompletionEquivSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationNativeCompletionEquivSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationNativeCompletionEquivSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationNativeCompletionEquivSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationNativeCompletionEquivSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Keep Mathlib's native Hilbert tensor norm explicit on the algebraic
physical excitation tensor carrier whose completion is being identified. -/
@[reducible] local instance osBoundaryExcitationNativeCompletionEquivNormedAddCommGroup
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

/-- The matching native tensor inner product. -/
@[reducible] local instance osBoundaryExcitationNativeCompletionEquivInnerProductSpace
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

/-- The concrete pair-Hilbert excitation sector is complete because it is the
closed topological closure of the algebraic excitation image in pair-`L²`. -/
local instance osBoundaryExcitationNativeCompletionEquivPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The exact algebraic excitation isometry has dense range in the concrete
pair-Hilbert sector.  This is not an extra analytic input: the target sector
was defined to be precisely the topological closure of this algebraic image. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_denseRange
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    DenseRange
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
        H N hN beta hbeta) := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  change
    y ∈ closure
      (((↑) :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →
            PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) ''
        Set.range
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta))
  rw [← Set.range_comp]
  have h_range :
      Set.range
          (((↑) :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →
                PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) ∘
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
              H N hN beta hbeta) =
        Set.range
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
            H N hN beta hbeta) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simpa [Function.comp_def] using
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_coe
          H N hN beta hbeta x
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simpa [Function.comp_def] using
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_coe
          H N hN beta hbeta x).symm
  rw [h_range]
  simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairAlgebraicRange,
      Submodule.topologicalClosure_coe,
      LinearMap.coe_range] using hy

/-- Canonical native Hilbert completion of the physical excitation algebraic
tensor core, identified isometrically and surjectively with the concrete
closed pair-`L²` excitation sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    UniformSpace.Completion
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta) ≃ₗᵢ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  denseLinearIsometryCompletionEquiv
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_denseRange
      H N hN beta hbeta)

/-- Exact compatibility with the canonical dense copy of the algebraic tensor
core: the completed equivalence restricts to the pre-existing sector-valued
algebraic excitation embedding. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector_apply_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
        H N hN beta hbeta
        (x : UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
        H N hN beta hbeta x := by
  exact denseLinearIsometryCompletionEquiv_apply_coe
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_denseRange
      H N hN beta hbeta)
    x

/-- Ambient pair-`L²` receipt for the same compatibility: on every algebraic
excitation tensor, the completed equivalence is exactly the original canonical
endpoint-pair embedding `J`. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector_apply_coe_pairL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
          H N hN beta hbeta
          (x : UniformSpace.Completion
            (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
              H N hN beta hbeta)) :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) =
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
      H N hN beta hbeta x := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector_apply_coe]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_coe
      H N hN beta hbeta x

end

end MathlibAnalytic
end MGAP4D
