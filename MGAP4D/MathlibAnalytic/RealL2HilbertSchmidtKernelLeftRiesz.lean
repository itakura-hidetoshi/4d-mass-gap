import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelBilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-!
# Left Riesz representative of a real product-L² Hilbert--Schmidt kernel

For a product kernel `K ∈ L²(μ × ν)` and a fixed right test vector `g`,
the bilinear kernel pairing

`f ↦ ⟪K, f ⊠ g⟫`

is a bounded real-linear functional on `L²(μ)`.  This file packages its
Fréchet--Riesz representative.  The existing rectangular kernel operator
packages the opposite direction (fixed left test vector); the present receipt
supplies the symmetric left-hand tool needed for independent endpoint
Gauss-law descent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- The Fréchet--Riesz vector in the left `L²` space representing the
functional `f ↦ ⟪K, f ⊠ g⟫`. -/
noncomputable def realL2HilbertSchmidtKernelLeftRieszVector
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (g : Lp ℝ 2 ν) : Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm
    ((realL2HilbertSchmidtKernelBilinear K).flip g)

/-- Exact kernel pairing represented by the left Riesz vector. -/
theorem realL2HilbertSchmidtKernelLeftRieszVector_inner
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ)
    (g : Lp ℝ 2 ν) :
    inner ℝ (realL2HilbertSchmidtKernelLeftRieszVector K g) f =
      realL2HilbertSchmidtKernelPairing K f g := by
  simpa [realL2HilbertSchmidtKernelLeftRieszVector] using
    (InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := Lp ℝ 2 μ)
      ((realL2HilbertSchmidtKernelBilinear K).flip g) f)

/-- The left Riesz representative has exactly the norm of the flipped
continuous dual functional. -/
theorem realL2HilbertSchmidtKernelLeftRieszVector_norm
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (g : Lp ℝ 2 ν) :
    ‖realL2HilbertSchmidtKernelLeftRieszVector K g‖ =
      ‖(realL2HilbertSchmidtKernelBilinear K).flip g‖ := by
  simpa [realL2HilbertSchmidtKernelLeftRieszVector] using
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm.norm_map
      ((realL2HilbertSchmidtKernelBilinear K).flip g)

/-- Sharp Hilbert--Schmidt bound for the left Riesz representative. -/
theorem realL2HilbertSchmidtKernelLeftRieszVector_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (g : Lp ℝ 2 ν) :
    ‖realL2HilbertSchmidtKernelLeftRieszVector K g‖ ≤
      ‖K‖ * ‖g‖ := by
  rw [realL2HilbertSchmidtKernelLeftRieszVector_norm]
  apply ContinuousLinearMap.opNorm_le_bound
    ((realL2HilbertSchmidtKernelBilinear K).flip g)
    (mul_nonneg (norm_nonneg K) (norm_nonneg g))
  intro f
  change
    ‖realL2HilbertSchmidtKernelPairing K f g‖ ≤
      (‖K‖ * ‖g‖) * ‖f‖
  calc
    ‖realL2HilbertSchmidtKernelPairing K f g‖ ≤
        ‖K‖ * ‖f‖ * ‖g‖ :=
      realL2HilbertSchmidtKernelPairing_norm_le K f g
    _ = (‖K‖ * ‖g‖) * ‖f‖ := by ring

/-- Audit-visible left-Riesz package. -/
structure RealL2HilbertSchmidtKernelLeftRieszPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) : Prop where
  pairing :
    ∀ (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν),
      inner ℝ (realL2HilbertSchmidtKernelLeftRieszVector K g) f =
        realL2HilbertSchmidtKernelPairing K f g
  normBound :
    ∀ g : Lp ℝ 2 ν,
      ‖realL2HilbertSchmidtKernelLeftRieszVector K g‖ ≤
        ‖K‖ * ‖g‖

/-- Construct the generic left-Riesz receipt. -/
theorem realL2HilbertSchmidtKernelLeftRieszPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    RealL2HilbertSchmidtKernelLeftRieszPackage K :=
  { pairing := realL2HilbertSchmidtKernelLeftRieszVector_inner K
    normBound := realL2HilbertSchmidtKernelLeftRieszVector_norm_le K }

end

end MathlibAnalytic
end MGAP4D
