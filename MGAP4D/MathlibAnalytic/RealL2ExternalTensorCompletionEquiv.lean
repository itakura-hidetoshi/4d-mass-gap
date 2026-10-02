import MGAP4D.MathlibAnalytic.DenseLinearIsometryCompletionEquiv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometry
import MGAP4D.MathlibAnalytic.RealL2ExternalTensorDenseRange
import Mathlib.Tactic

/-!
# Canonical Hilbert completion of the real L² external tensor

For finite measures `μ` and `ν`, the algebraic external-tensor realization

`L²(μ) ⊗ L²(ν) → L²(μ × ν)`

is already known to be an exact linear isometry, and #5024 proves that its
range is dense.  Mathlib's canonical uniform completion therefore identifies
isometrically and surjectively with the full product-`L²` space.

This file packages that identification as a genuine `LinearIsometryEquiv`.
It is the completion-level bridge needed to transport tensorized Gauss
projections and independent endpoint gauge actions without introducing any
ad hoc completion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

@[reducible] local instance realL2ExternalTensorCompletionNormedAddCommGroup
    [SFinite μ] [SFinite ν] :
    NormedAddCommGroup (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ) (E := Lp ℝ 2 μ) (F := Lp ℝ 2 ν)

@[reducible] local instance realL2ExternalTensorCompletionInnerProductSpace
    [SFinite μ] [SFinite ν] :
    InnerProductSpace ℝ (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ) (E := Lp ℝ 2 μ) (F := Lp ℝ 2 ν)

/-- The exact algebraic external-tensor linear isometry has dense range in the
full product-`L²` Hilbert space. -/
theorem realL2ExternalTensorLiftLinearIsometry_denseRange
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    DenseRange
      (realL2ExternalTensorLiftLinearIsometry
        (μ := μ) (ν := ν)) := by
  simpa only [realL2ExternalTensorLiftLinearIsometry_apply] using
    (realL2ExternalTensorLift_denseRange (μ := μ) (ν := ν))

/-- Canonical isometric equivalence between Mathlib's completion of the
algebraic Hilbert tensor product and the full real product-`L²` space. -/
noncomputable def realL2ExternalTensorHilbertCompletionEquiv
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    UniformSpace.Completion (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (μ.prod ν) :=
  denseLinearIsometryCompletionEquiv
    (realL2ExternalTensorLiftLinearIsometry
      (μ := μ) (ν := ν))
    (realL2ExternalTensorLiftLinearIsometry_denseRange
      (μ := μ) (ν := ν))

/-- On the canonical dense copy of the algebraic tensor product, the completed
equivalence is exactly the original external-tensor lift. -/
@[simp] theorem realL2ExternalTensorHilbertCompletionEquiv_apply_coe
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    realL2ExternalTensorHilbertCompletionEquiv
        (μ := μ) (ν := ν)
        (x : UniformSpace.Completion
          (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν)) =
      realL2ExternalTensorLift x := by
  simpa only [realL2ExternalTensorLiftLinearIsometry_apply] using
    (denseLinearIsometryCompletionEquiv_apply_coe
      (realL2ExternalTensorLiftLinearIsometry
        (μ := μ) (ν := ν))
      (realL2ExternalTensorLiftLinearIsometry_denseRange
        (μ := μ) (ν := ν))
      x)

/-- Pure tensors are sent to the concrete pointwise external tensor in
product-`L²`. -/
@[simp] theorem realL2ExternalTensorHilbertCompletionEquiv_tmul
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Lp ℝ 2 μ)
    (g : Lp ℝ 2 ν) :
    realL2ExternalTensorHilbertCompletionEquiv
        (μ := μ) (ν := ν)
        ((f ⊗ₜ[ℝ] g : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
          UniformSpace.Completion
            (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν)) =
      realL2ExternalTensor f g := by
  rw [realL2ExternalTensorHilbertCompletionEquiv_apply_coe,
    realL2ExternalTensorLift_tmul]

/-- Audit-visible completion receipt. -/
structure RealL2ExternalTensorCompletionEquivPackage
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : Prop where
  algebraicDense :
    DenseRange
      (realL2ExternalTensorLiftLinearIsometry
        (μ := μ) (ν := ν))
  pureTensor :
    ∀ (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν),
      realL2ExternalTensorHilbertCompletionEquiv
          (μ := μ) (ν := ν)
          ((f ⊗ₜ[ℝ] g : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
            UniformSpace.Completion
              (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν)) =
        realL2ExternalTensor f g

/-- Construct the canonical product-`L²` Hilbert-completion package. -/
theorem realL2ExternalTensorCompletionEquivPackage
    [SFinite μ] [SFinite ν]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    RealL2ExternalTensorCompletionEquivPackage
      (μ := μ) (ν := ν) :=
  { algebraicDense :=
      realL2ExternalTensorLiftLinearIsometry_denseRange
        (μ := μ) (ν := ν)
    pureTensor :=
      realL2ExternalTensorHilbertCompletionEquiv_tmul
        (μ := μ) (ν := ν) }

end

end MathlibAnalytic
end MGAP4D
