import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationHilbertTensorCompletion
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

universe u v

/-- Keep Mathlib's native Hilbert tensor norm explicit on the real `L²`
algebraic tensor carrier. -/
local instance realL2ExternalTensorLiftNormedAddCommGroup
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    NormedAddCommGroup (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ) (E := Lp ℝ 2 μ) (F := Lp ℝ 2 ν)

/-- Keep the corresponding native Mathlib tensor inner product explicit. -/
local instance realL2ExternalTensorLiftInnerProductSpace
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    InnerProductSpace ℝ (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ) (E := Lp ℝ 2 μ) (F := Lp ℝ 2 ν)

/-- The universal external-tensor lift preserves the full native Mathlib
inner product on the algebraic Hilbert tensor product. -/
theorem realL2ExternalTensorLift_inner
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (x y : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensorLift x) (realL2ExternalTensorLift y) =
      inner ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, inner_zero_left, inner_zero_left]
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, inner_zero_right, inner_zero_right]
      | tmul f' g' =>
          rw [realL2ExternalTensorLift_tmul, realL2ExternalTensorLift_tmul,
            realL2ExternalTensor_inner, TensorProduct.inner_tmul]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, inner_add_right, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, inner_add_left, inner_add_left, hx₁, hx₂]

/-- The real `L²` external-tensor lift is an exact linear isometry for
Mathlib's native algebraic Hilbert tensor norm. -/
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

/-- In particular the universal real `L²` external-tensor lift is injective on
the whole algebraic tensor product. -/
theorem realL2ExternalTensorLift_injective
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    Function.Injective
      (realL2ExternalTensorLift (μ := μ) (ν := ν)) := by
  intro x y hxy
  exact
    (realL2ExternalTensorLiftLinearIsometry
      (μ := μ) (ν := ν)).injective hxy

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

/-- The underlying one-slice physical excitation inclusion is injective. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap_injective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
        H N hN beta hbeta) := by
  intro f g hfg
  change periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
      H N hN beta hbeta f =
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
      H N hN beta hbeta g at hfg
  apply Subtype.ext
  apply Subtype.ext
  exact hfg

/-- Tensoring the physical one-slice inclusion with itself remains injective.
This is proved algebraically using flatness of real vector spaces, avoiding any
replacement of the canonical tensor-product module instance. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorMap_injective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Injective
      (TensorProduct.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
          H N hN beta hbeta)) := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta
  let L :=
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
  let f : K →ₗ[ℝ] L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
      H N hN beta hbeta
  have hf : Function.Injective f :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap_injective
      H N hN beta hbeta
  have hr : Function.Injective (f.rTensor K) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := K) f hf
  have hl : Function.Injective (f.lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) f hf
  intro x y hxy
  change TensorProduct.map f f x = TensorProduct.map f f y at hxy
  rw [← LinearMap.lTensor_comp_rTensor] at hxy
  simp only [LinearMap.comp_apply] at hxy
  exact hr (hl hxy)

/-- The pre-existing canonical physical algebraic tensor embedding is
injective on the whole algebraic tensor core.  Its two constituent maps are
faithful: the factor map by flatness and the external `L²` realization by the
Hilbert-tensor isometry above. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_injective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta) := by
  intro x y hxy
  change
    realL2ExternalTensorLift
        (TensorProduct.map
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
            H N hN beta hbeta) x) =
      realL2ExternalTensorLift
        (TensorProduct.map
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
            H N hN beta hbeta) y) at hxy
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorMap_injective
      H N hN beta hbeta
  exact realL2ExternalTensorLift_injective hxy

/-- The completed physical excitation sector is exactly the topological
closure of this faithful algebraic tensor image. -/
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

/-- Audit-visible receipt that the physical excitation algebraic tensor core
has a faithful concrete pair-`L²` realization, with exact cross norm on pure
tensors and the closed Hilbert sector as its topological completion. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometryPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  oneSliceInjective :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
        H N hN beta hbeta)
  tensorFactorInjective :
    Function.Injective
      (TensorProduct.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
          H N hN beta hbeta))
  canonicalInjective :
    Function.Injective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta)
  pureTensorCrossNorm :
    ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖ = ‖f‖ * ‖g‖
  completedSector :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta =
      (LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta)).topologicalClosure

/-- Construct the faithful algebraic-tensor realization package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometryPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometryPackage
      H N hN beta hbeta :=
  { oneSliceInjective :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap_injective
        H N hN beta hbeta
    tensorFactorInjective :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorMap_injective
        H N hN beta hbeta
    canonicalInjective :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_injective
        H N hN beta hbeta
    pureTensorCrossNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul_norm
        H N hN beta hbeta
    completedSector :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_eq_topologicalClosure_range
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
