import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationHilbertTensorCompletion
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

universe u v

/-- The concrete real `L²` external tensor preserves the Hilbert tensor
inner product on decomposable vectors. -/
theorem realL2ExternalTensor_inner
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (f₁ f₂ : Lp ℝ 2 μ) (g₁ g₂ : Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensor f₁ g₁) (realL2ExternalTensor f₂ g₂) =
      inner ℝ f₁ f₂ * inner ℝ g₁ g₂ := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ z, inner ℝ (realL2ExternalTensor f₁ g₁ z)
          (realL2ExternalTensor f₂ g₂ z) ∂(μ.prod ν)) =
        ∫ z : α × β,
          inner ℝ (f₁ z.1) (f₂ z.1) *
            inner ℝ (g₁ z.2) (g₂ z.2) ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards [realL2ExternalTensor_coeFn f₁ g₁,
        realL2ExternalTensor_coeFn f₂ g₂] with z h₁ h₂
      rw [h₁, h₂]
      simp [realL2ExternalTensorFunction]
    _ = (∫ a, inner ℝ (f₁ a) (f₂ a) ∂μ) *
        ∫ b, inner ℝ (g₁ b) (g₂ b) ∂ν := by
      exact integral_prod_mul
        (fun a => inner ℝ (f₁ a) (f₂ a))
        (fun b => inner ℝ (g₁ b) (g₂ b))
    _ = inner ℝ f₁ f₂ * inner ℝ g₁ g₂ := by
      rw [← MeasureTheory.L2.inner_def, ← MeasureTheory.L2.inner_def]

/-- The universal external-tensor lift preserves the full native Mathlib
inner product on the algebraic Hilbert tensor product, not only on pure
tensors. -/
theorem realL2ExternalTensorLift_inner
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (x y : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensorLift x) (realL2ExternalTensorLift y) =
      inner ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          rw [realL2ExternalTensorLift_tmul, realL2ExternalTensorLift_tmul,
            realL2ExternalTensor_inner, TensorProduct.inner_tmul]
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, inner_add_left, hx₁, hx₂]

/-- The real `L²` external-tensor lift is therefore an exact linear isometry
for Mathlib's native algebraic Hilbert tensor norm. -/
noncomputable def realL2ExternalTensorLiftLinearIsometry
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  realL2ExternalTensorLift.isometryOfInner realL2ExternalTensorLift_inner

@[simp] theorem realL2ExternalTensorLiftLinearIsometry_apply
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (x : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    realL2ExternalTensorLiftLinearIsometry x = realL2ExternalTensorLift x :=
  rfl

local instance osBoundaryExcitationAlgebraicTensorIsometrySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationAlgebraicTensorIsometrySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationAlgebraicTensorIsometrySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationAlgebraicTensorIsometrySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationAlgebraicTensorIsometrySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationAlgebraicTensorIsometrySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationAlgebraicTensorIsometrySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Forgetting the physical invariant-subspace wrappers is an exact linear
isometry into the one-slice Haar `L²` carrier. -/
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

/-- The existing algebraic physical excitation realization is an exact linear
isometry from Mathlib's native algebraic Hilbert tensor product into the
ordered endpoint-pair Haar `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftLinearIsometry
    (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (TensorProduct.mapIsometry
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorLinearIsometry_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorLinearIsometry
        H N hN beta hbeta x =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x :=
  rfl

/-- Full algebraic-tensor norm preservation, extending the earlier pure-tensor
cross-norm theorem to arbitrary finite linear combinations. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x‖ = ‖x‖ := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorLinearIsometry
      H N hN beta hbeta).norm_map x

/-- Hence the concrete algebraic excitation embedding is injective on the full
tensor core. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_injective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorLinearIsometry
      H N hN beta hbeta).injective

/-- The isometric algebraic tensor realization with codomain restricted to the
completed closed excitation Hilbert sector constructed in the previous layer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta where
  toLinearMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector
      H N hN beta hbeta
  norm_map' := by
    intro x
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x‖ = ‖x‖
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
        H N hN beta hbeta x

/-- The completed physical excitation sector is exactly the topological
closure of the range of this isometric algebraic tensor realization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_eq_topologicalClosure_range
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta =
      (LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta)).topologicalClosure :=
  rfl

/-- Audit-visible receipt that the algebraic excitation tensor core carries
Mathlib's native Hilbert tensor norm and embeds isometrically and injectively
into the concrete completed pair sector. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometryPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  fullNorm :
    ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖ = ‖x‖
  injective :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta)
  completedSector :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta =
      (LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta)).topologicalClosure

/-- Construct the full algebraic-tensor isometry package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometryPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometryPackage
      H N hN beta hbeta :=
  { fullNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
        H N hN beta hbeta
    injective :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_injective
        H N hN beta hbeta
    completedSector :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_eq_topologicalClosure_range
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
