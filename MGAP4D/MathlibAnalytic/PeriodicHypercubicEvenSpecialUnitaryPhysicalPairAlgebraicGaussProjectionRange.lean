import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedSector
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorCore
import Mathlib.Tactic

/-!
# Algebraic tensor-square realization of the finite-volume Gauss projection

Let `P_G` be the orthogonal one-slice Gauss-law projection.  On the algebraic
tensor square of the ambient spatial-slice Haar `L²` space, Mathlib's
`TensorProduct.map` gives the exact tensorwise projection `P_G ⊗ P_G`.
Realizing algebraic tensors as product-Haar kernels with
`realL2ExternalTensorLift` yields precisely the algebraic physical-pair span.

The main equality is

`range (realL2ExternalTensorLift ∘ (P_G ⊗ P_G)) = PhysicalPairSpan`.

Consequently the already-defined completed physical pair carrier is exactly the
topological closure of this concrete tensorwise-Gauss-projected range.  This is
the algebraic range half of H1-D4; the remaining step is the ambient
Hilbert-completion/dense-range argument identifying that closure with the full
independent-endpoint gauge fixed sector.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance physicalPairAlgebraicGaussTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairAlgebraicGaussCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairAlgebraicGaussSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairAlgebraicGaussMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairAlgebraicGaussBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairAlgebraicGaussSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairAlgebraicGaussSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Tensorwise one-slice Gauss-law projection on the algebraic tensor square of
ambient spatial-slice Haar `L²`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection
    (H N : ℕ) :
    (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) →ₗ[ℝ]
    (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.map
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).toLinearMap
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N).toLinearMap

@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection_tmul
    (H N : ℕ)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection H N
        (f ⊗ₜ[ℝ] g) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f ⊗ₜ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g := by
  rfl

/-- Concrete product-Haar realization of the tensorwise algebraic Gauss
projection. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
    (H N : ℕ) :
    (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensorLift.comp
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjection H N)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_tmul
    (H N : ℕ)
    (f g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
        H N (f ⊗ₜ[ℝ] g) =
      realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g) := by
  rfl

/-- Every algebraic tensorwise-Gauss-projected kernel belongs to the algebraic
physical-pair span. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_range_le_physicalPairSpan
    (H N : ℕ) :
    LinearMap.range
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N := by
  rintro z ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul f g =>
      let pf :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
        ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N f,
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem H N f⟩
      let pg :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
        ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N g,
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_mem H N g⟩
      change realL2ExternalTensor (pf : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
          (pg : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N
      apply Submodule.subset_span
      exact ⟨(pf, pg), rfl⟩
  | add x y hx hy =>
      rw [map_add]
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).add_mem hx hy

/-- Every decomposable physical-pair generator is realized by first applying
the one-slice Gauss projection to an ambient pure tensor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairGeneratorSet_subset_algebraicGaussProjectionRealization_range
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairGeneratorSet H N ⊆
      LinearMap.range
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N) := by
  rintro z ⟨⟨x, y⟩, rfl⟩
  have hx :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
          (x : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
        (x : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff
      H N _).2 x.property
  have hy :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection H N
          (y : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
        (y : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaussLawProjection_eq_self_iff
      H N _).2 y.property
  refine ⟨
    (x : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ⊗ₜ[ℝ]
      (y : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)), ?_⟩
  rw [
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_tmul,
    hx, hy]
  rfl

/-- Exact algebraic range theorem: the realized tensor square of the one-slice
orthogonal Gauss projection has precisely the already-defined physical-pair
span as its range. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_range
    (H N : ℕ) :
    LinearMap.range
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N := by
  apply le_antisymm
  · exact
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_range_le_physicalPairSpan
        H N
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan]
    exact Submodule.span_le.2
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairGeneratorSet_subset_algebraicGaussProjectionRealization_range
        H N)

/-- The completed physical pair carrier is exactly the closure of the concrete
algebraic tensorwise-Gauss-projected range. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_algebraicGaussProjectionRealization_range_topologicalClosure
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N =
      (LinearMap.range
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N)).topologicalClosure := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_range]

/-- Audit-visible H1-D4 algebraic tensor-square Gauss projection receipt. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicGaussProjectionRangePackage
    (H N : ℕ) : Prop where
  rangeEq :
    LinearMap.range
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N
  carrierClosure :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N =
      (LinearMap.range
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization
          H N)).topologicalClosure

/-- Construct the algebraic tensor-square Gauss projection range package. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicGaussProjectionRangePackage
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicGaussProjectionRangePackage
      H N :=
  { rangeEq :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairAlgebraicGaussProjectionRealization_range
        H N
    carrierClosure :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_algebraicGaussProjectionRealization_range_topologicalClosure
        H N }

end

end MathlibAnalytic
end MGAP4D
