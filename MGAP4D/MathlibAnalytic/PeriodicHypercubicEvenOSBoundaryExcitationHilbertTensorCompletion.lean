import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationHilbertSchmidtOperatorCore
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

universe u v

/-- The real `L²` external tensor preserves the Hilbert inner product on pure
factors.  This is the product-measure identity underlying the Hilbert tensor
completion used below. -/
theorem realL2ExternalTensor_inner
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (f₁ f₂ : Lp ℝ 2 μ) (g₁ g₂ : Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensor f₁ g₁)
        (realL2ExternalTensor f₂ g₂) =
      inner ℝ f₁ f₂ * inner ℝ g₁ g₂ := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ z,
        inner ℝ (realL2ExternalTensor f₁ g₁ z)
          (realL2ExternalTensor f₂ g₂ z) ∂(μ.prod ν)) =
      ∫ z : α × β,
        inner ℝ (f₁ z.1) (f₂ z.1) *
          inner ℝ (g₁ z.2) (g₂ z.2) ∂(μ.prod ν) := by
        apply integral_congr_ae
        filter_upwards
          [realL2ExternalTensor_coeFn f₁ g₁,
           realL2ExternalTensor_coeFn f₂ g₂] with z h₁ h₂
        rw [h₁, h₂]
        simp only [realL2ExternalTensorFunction, Real.inner_apply]
        ring
    _ =
      (∫ a, inner ℝ (f₁ a) (f₂ a) ∂μ) *
        (∫ b, inner ℝ (g₁ b) (g₂ b) ∂ν) := by
      exact integral_prod_mul
        (fun a => inner ℝ (f₁ a) (f₂ a))
        (fun b => inner ℝ (g₁ b) (g₂ b))
    _ = inner ℝ f₁ f₂ * inner ℝ g₁ g₂ := by
      rw [← MeasureTheory.L2.inner_def, ← MeasureTheory.L2.inner_def]

/-- The universal external-tensor lift is inner-product preserving on the
whole algebraic Hilbert tensor product, not merely on pure tensors. -/
theorem realL2ExternalTensorLift_inner
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (x y : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensorLift x)
        (realL2ExternalTensorLift y) =
      inner ℝ x y := by
  refine x.induction_on ?_ ?_ ?_
  · simp
  · intro f g
    refine y.induction_on ?_ ?_ ?_
    · simp
    · intro f' g'
      simpa only [realL2ExternalTensorLift_tmul, TensorProduct.inner_tmul] using
        (realL2ExternalTensor_inner f f' g g')
    · intro y₁ y₂ hy₁ hy₂
      simp [hy₁, hy₂, inner_add_right]
  · intro x₁ x₂ hx₁ hx₂
    simp [hx₁, hx₂, inner_add_left]

/-- The real `L²` external-tensor lift as a genuine linear isometry from the
Mathlib Hilbert norm on the algebraic tensor product into product-measure
`L²`. -/
noncomputable def realL2ExternalTensorLiftIsometry
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  (realL2ExternalTensorLift (μ := μ) (ν := ν)).isometryOfInner
    (realL2ExternalTensorLift_inner (μ := μ) (ν := ν))

@[simp] theorem realL2ExternalTensorLiftIsometry_apply
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (x : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    realL2ExternalTensorLiftIsometry (μ := μ) (ν := ν) x =
      realL2ExternalTensorLift x :=
  rfl

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

/-- Forgetting the physical excitation subtype wrappers is an isometric linear
embedding into the one-slice Haar `L²` Hilbert space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗᵢ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) where
  toLinearMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
      H N hN beta hbeta
  norm_map' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_norm
      H N hN beta hbeta

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta f :=
  rfl

/-- The existing physical algebraic excitation tensor embedding is a linear
isometry for Mathlib's canonical Hilbert tensor norm. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftIsometry
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (TensorProduct.mapIsometry
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry
        H N hN beta hbeta x =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x :=
  rfl

/-- Full algebraic-tensor norm preservation, upgrading the earlier pure-tensor
cross-norm theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x‖ = ‖x‖ := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry_apply]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry
      H N hN beta hbeta).norm_map x

/-- The physical algebraic excitation tensor realization has no kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_injective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta) := by
  intro x y hxy
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry
      H N hN beta hbeta).injective
  simpa only
    [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry_apply]
    using hxy

/-- Canonical Hilbert completion of the physical two-endpoint excitation
algebraic tensor product. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Type :=
  UniformSpace.Completion
    (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta)

/-- Extend the full algebraic tensor isometry to the canonical completed
physical excitation Hilbert tensor sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingIsometry
    H N hN beta hbeta).fromCompletion

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding
        H N hN beta hbeta
        (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding]
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

/-- The algebraic tensor core is dense in its canonical Hilbert completion. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore_dense
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    DenseRange
      (fun x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta =>
        (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
          H N hN beta hbeta)) :=
  UniformSpace.Completion.denseRange_coe

/-- The completed excitation sector embeds isometrically into the actual shared
Wilson boundary `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N :=
  (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding
        H N hN beta hbeta
        (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
          H N hN beta hbeta) =
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x) := by
  rfl

/-- Exact norm preservation on the completed pair-`L²` realization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding
        H N hN beta hbeta x‖ = ‖x‖ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding
    H N hN beta hbeta).norm_map x

/-- Exact norm preservation on the completed shared-boundary realization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding
        H N hN beta hbeta x‖ = ‖x‖ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding
    H N hN beta hbeta).norm_map x

/-- Audit-visible receipt that the physical two-endpoint excitation algebraic
tensor has been promoted to its canonical Hilbert completion and embedded
isometrically into both the pair and actual boundary `L²` carriers. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationHilbertTensorCompletionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  algebraicNorm :
    ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖ = ‖x‖
  algebraicInjective :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta)
  algebraicCoreDense :
    DenseRange
      (fun x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta =>
        (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
          H N hN beta hbeta))
  pairCompletionNorm :
    ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding
          H N hN beta hbeta x‖ = ‖x‖
  boundaryCompletionNorm :
    ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorCompletion
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding
          H N hN beta hbeta x‖ = ‖x‖

/-- Construct the completed physical excitation Hilbert tensor package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationHilbertTensorCompletionPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationHilbertTensorCompletionPackage
      H N hN beta hbeta :=
  { algebraicNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
        H N hN beta hbeta
    algebraicInjective :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_injective
        H N hN beta hbeta
    algebraicCoreDense :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore_dense
        H N hN beta hbeta
    pairCompletionNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorPairEmbedding_norm
        H N hN beta hbeta
    boundaryCompletionNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationHilbertTensorBoundaryEmbedding_norm
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
