import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationHilbertTensorCompletion
import Mathlib.Analysis.InnerProductSpace.TensorProduct
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

/-- Keep the corresponding native Mathlib tensor inner product explicit on the
real `L²` algebraic tensor carrier. -/
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

/-- Keep only the native tensor norm permanently visible on the physical
algebraic core.  In particular this does not replace the canonical tensor
module instance used by the already-compiled embedding. -/
local instance osBoundaryExcitationAlgebraicTensorIsometryPhysicalTensorNormedAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta
  change NormedAddCommGroup (K ⊗[ℝ] K)
  exact TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ) (E := K) (F := K)

/-- Expose only the native tensor `Inner` operation on the physical algebraic
core.  The complete inner-product-space structure is kept local to proofs that
need the norm/inner compatibility, avoiding a competing module instance. -/
local instance osBoundaryExcitationAlgebraicTensorIsometryPhysicalTensorInner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Inner ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta
  change Inner ℝ (K ⊗[ℝ] K)
  exact
    (TensorProduct.instInnerProductSpace
      (𝕜 := ℝ) (E := K) (F := K)).toInner

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

/-- The nested physical-subspace inclusion also preserves the exact real inner
product, definitionally. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
          H N hN beta hbeta g) =
      inner ℝ f g :=
  rfl

/-- The existing physical algebraic tensor embedding preserves the full native
Mathlib tensor inner product.  The proof is purely algebraic induction, so the
canonical embedding is never rebundled under a second module-instance path. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x y : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta y) =
      inner ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, inner_zero_left, inner_zero_left]
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, inner_zero_right, inner_zero_right]
      | tmul f' g' =>
          rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul,
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul]
          unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
          rw [realL2ExternalTensor_inner, TensorProduct.inner_tmul,
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_inner,
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_inner]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, inner_add_right, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, inner_add_left, inner_add_left, hx₁, hx₂]

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
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta
  letI : InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) := by
    change InnerProductSpace ℝ (K ⊗[ℝ] K)
    exact TensorProduct.instInnerProductSpace
      (𝕜 := ℝ) (E := K) (F := K)
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x‖ =
        √(RCLike.re
          (inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
              H N hN beta hbeta x)
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
              H N hN beta hbeta x))) :=
      norm_eq_sqrt_re_inner _
    _ = √(RCLike.re (inner ℝ x x)) := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_inner]
    _ = ‖x‖ := (norm_eq_sqrt_re_inner x).symm

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
  intro x y hxy
  have hzero :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnorm : ‖x - y‖ = 0 := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
      H N hN beta hbeta (x - y), hzero, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The existing codrestricted algebraic realization preserves the same native
tensor norm inside the completed closed excitation sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector
        H N hN beta hbeta x‖ = ‖x‖ := by
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
  fullInner :
    ∀ x y : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
            H N hN beta hbeta x)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
            H N hN beta hbeta y) =
        inner ℝ x y
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
  { fullInner :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_inner
        H N hN beta hbeta
    fullNorm :=
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
