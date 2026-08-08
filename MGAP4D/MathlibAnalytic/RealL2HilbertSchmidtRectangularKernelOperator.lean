import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelBilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- The Fréchet--Riesz vector in the right `L²` space representing the
rectangular Hilbert--Schmidt kernel functional
`g ↦ ⟪K, f ⊠ g⟫`. -/
noncomputable def realL2HilbertSchmidtRectangularKernelRieszVector
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) : Lp ℝ 2 ν :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 ν)).symm
    (realL2HilbertSchmidtKernelBilinear K f)

/-- Exact matrix coefficient of the rectangular Riesz representative. -/
theorem realL2HilbertSchmidtRectangularKernelRieszVector_inner
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    inner ℝ (realL2HilbertSchmidtRectangularKernelRieszVector K f) g =
      realL2HilbertSchmidtKernelPairing K f g := by
  simpa [realL2HilbertSchmidtRectangularKernelRieszVector] using
    (InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := Lp ℝ 2 ν)
      (realL2HilbertSchmidtKernelBilinear K f) g)

/-- The rectangular Riesz representative has the norm of its dual
functional. -/
theorem realL2HilbertSchmidtRectangularKernelRieszVector_norm
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) :
    ‖realL2HilbertSchmidtRectangularKernelRieszVector K f‖ =
      ‖realL2HilbertSchmidtKernelBilinear K f‖ := by
  simpa [realL2HilbertSchmidtRectangularKernelRieszVector] using
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 ν)).symm.norm_map
      (realL2HilbertSchmidtKernelBilinear K f)

/-- Sharp Hilbert--Schmidt bound for the rectangular Riesz representative. -/
theorem realL2HilbertSchmidtRectangularKernelRieszVector_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) :
    ‖realL2HilbertSchmidtRectangularKernelRieszVector K f‖ ≤
      ‖K‖ * ‖f‖ := by
  rw [realL2HilbertSchmidtRectangularKernelRieszVector_norm]
  exact realL2HilbertSchmidtKernelBilinear_apply_norm_le K f

/-- Additivity of the rectangular Riesz representative in the left test
vector. -/
theorem realL2HilbertSchmidtRectangularKernelRieszVector_add
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f₁ f₂ : Lp ℝ 2 μ) :
    realL2HilbertSchmidtRectangularKernelRieszVector K (f₁ + f₂) =
      realL2HilbertSchmidtRectangularKernelRieszVector K f₁ +
        realL2HilbertSchmidtRectangularKernelRieszVector K f₂ := by
  simp [realL2HilbertSchmidtRectangularKernelRieszVector]

/-- Real scalar linearity of the rectangular Riesz representative. -/
theorem realL2HilbertSchmidtRectangularKernelRieszVector_smul
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (c : ℝ) (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtRectangularKernelRieszVector K (c • f) =
      c • realL2HilbertSchmidtRectangularKernelRieszVector K f := by
  simp [realL2HilbertSchmidtRectangularKernelRieszVector]

/-- Unbundled rectangular real-linear Hilbert--Schmidt kernel operator. -/
noncomputable def realL2HilbertSchmidtRectangularKernelOperatorLinearMap
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν :=
  { toFun := realL2HilbertSchmidtRectangularKernelRieszVector K
    map_add' := realL2HilbertSchmidtRectangularKernelRieszVector_add K
    map_smul' := realL2HilbertSchmidtRectangularKernelRieszVector_smul K }

/-- Canonical bounded rectangular operator associated by Fréchet--Riesz to a
real product-`L²` kernel. -/
noncomputable def realL2HilbertSchmidtRectangularKernelOperator
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    (𝕜 := ℝ)
    (𝕜₂ := ℝ)
    (E := Lp ℝ 2 μ)
    (F := Lp ℝ 2 ν)
    (σ := RingHom.id ℝ)
    (realL2HilbertSchmidtRectangularKernelOperatorLinearMap K)
    ‖K‖
    (realL2HilbertSchmidtRectangularKernelRieszVector_norm_le K)

@[simp] theorem realL2HilbertSchmidtRectangularKernelOperator_apply
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtRectangularKernelOperator K f =
      realL2HilbertSchmidtRectangularKernelRieszVector K f := by
  rfl

/-- Exact matrix coefficient of the rectangular Hilbert--Schmidt operator. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_inner
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    inner ℝ (realL2HilbertSchmidtRectangularKernelOperator K f) g =
      realL2HilbertSchmidtKernelPairing K f g := by
  exact realL2HilbertSchmidtRectangularKernelRieszVector_inner K f g

/-- Operator norm of the rectangular kernel operator is bounded by the kernel
`L²` norm. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ‖realL2HilbertSchmidtRectangularKernelOperator K‖ ≤ ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (realL2HilbertSchmidtRectangularKernelOperator K)
    (norm_nonneg K)
  intro f
  exact realL2HilbertSchmidtRectangularKernelRieszVector_norm_le K f

/-- Audit-visible generic rectangular Hilbert--Schmidt operator package. -/
structure RealL2HilbertSchmidtRectangularKernelOperatorPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) : Prop where
  innerFormula :
    ∀ (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν),
      inner ℝ (realL2HilbertSchmidtRectangularKernelOperator K f) g =
        realL2HilbertSchmidtKernelPairing K f g
  normBound :
    ‖realL2HilbertSchmidtRectangularKernelOperator K‖ ≤ ‖K‖

/-- Construct the generic rectangular Hilbert--Schmidt operator receipt. -/
theorem realL2HilbertSchmidtRectangularKernelOperatorPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    RealL2HilbertSchmidtRectangularKernelOperatorPackage K :=
  { innerFormula := realL2HilbertSchmidtRectangularKernelOperator_inner K
    normBound := realL2HilbertSchmidtRectangularKernelOperator_norm_le K }

end

end MathlibAnalytic
end MGAP4D
