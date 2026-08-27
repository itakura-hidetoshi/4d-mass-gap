import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationHilbertSchmidtOperatorCore
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance osBoundaryExcitationHilbertTensorCompletionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationHilbertTensorCompletionSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationHilbertTensorCompletionSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationHilbertTensorCompletionSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationHilbertTensorCompletionSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationHilbertTensorCompletionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationHilbertTensorCompletionSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The algebraic physical excitation tensors, realized concretely inside the
ordered endpoint-pair Haar `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairAlgebraicRange
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Submodule ℝ (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :=
  LinearMap.range
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
      H N hN beta hbeta)

/-- The completed physical two-endpoint excitation Hilbert sector is the
topological closure of the concrete algebraic tensor image in pair-`L²`.
Keeping the carrier as a `Submodule` uses Mathlib's native normed-space and
complete-space instances for `Submodule.topologicalClosure`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Submodule ℝ (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairAlgebraicRange
    H N hN beta hbeta).topologicalClosure

/-- Every algebraic excitation tensor lands in the completed pair-`L²`
excitation sector by construction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_mem_pairHilbertSector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta := by
  apply Submodule.le_topologicalClosure
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairAlgebraicRange
      H N hN beta hbeta)
  exact LinearMap.mem_range_self _ x

/-- The original algebraic tensor embedding, with codomain restricted to the
completed physical excitation Hilbert sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
    H N hN beta hbeta).codRestrict
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_mem_pairHilbertSector
        H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector
        H N hN beta hbeta x :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) =
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
      H N hN beta hbeta x :=
  rfl

/-- Pure physical excitation tensors lie in the completed sector with their
canonical endpoint-pair kernel representative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2_mem_pairHilbertSector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
        H N hN beta hbeta f g ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_mem_pairHilbertSector
      H N hN beta hbeta (f ⊗ₜ[ℝ] g)

/-- The concrete completed excitation sector is a closed subset of pair-`L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_isClosed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsClosed
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :
        Set (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)) := by
  exact Submodule.isClosed_topologicalClosure
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairAlgebraicRange
      H N hN beta hbeta)

/-- The topological-closure carrier is complete in the native Mathlib subtype
structure. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  inferInstance

/-- Inclusion of the completed excitation sector into pair-`L²` as an exact
linear isometry. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N where
  toLinearMap :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta).subtype
  norm_map' := fun _ => rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
        H N hN beta hbeta x =
      (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :=
  rfl

/-- The same completed sector embeds isometrically into the actual shared
Wilson-boundary `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N :=
  (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
        H N hN beta hbeta x =
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
        (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :=
  rfl

/-- Exact norm preservation in the concrete pair realization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
        H N hN beta hbeta x‖ = ‖x‖ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
    H N hN beta hbeta).norm_map x

/-- Exact norm preservation after transport to the actual shared boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
        H N hN beta hbeta x‖ = ‖x‖ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
    H N hN beta hbeta).norm_map x

/-- Audit-visible receipt that the physical algebraic excitation kernels have a
canonical concrete Hilbert completion as their closed image sector in pair
`L²`, with an isometric realization on the actual Wilson boundary. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationClosedHilbertSectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  algebraicImageMem :
    ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta
  closedSector :
    IsClosed
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :
        Set (PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N))
  pairNorm :
    ∀ x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
          H N hN beta hbeta x‖ = ‖x‖
  boundaryNorm :
    ∀ x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
          H N hN beta hbeta x‖ = ‖x‖

/-- Construct the concrete completed excitation Hilbert-sector package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationClosedHilbertSectorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationClosedHilbertSectorPackage
      H N hN beta hbeta :=
  { algebraicImageMem :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_mem_pairHilbertSector
        H N hN beta hbeta
    closedSector :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_isClosed
        H N hN beta hbeta
    pairNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_norm
        H N hN beta hbeta
    boundaryNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_norm
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
