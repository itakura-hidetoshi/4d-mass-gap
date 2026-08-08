import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Basic
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

/-- Hilbert--Schmidt kernel pairing against the exact real `L²` external tensor.
For `K ∈ L²(μ × ν)`, this is the bilinear form
`B_K(f,g) = ⟪K, f ⊠ g⟫_ℝ`. -/
def realL2HilbertSchmidtKernelPairing
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : ℝ :=
  inner ℝ K (realL2ExternalTensor f g)

/-- The Hilbert--Schmidt kernel pairing is additive in the left test vector. -/
theorem realL2HilbertSchmidtKernelPairing_add_left
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f₁ f₂ : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing K (f₁ + f₂) g =
      realL2HilbertSchmidtKernelPairing K f₁ g +
        realL2HilbertSchmidtKernelPairing K f₂ g := by
  simp [realL2HilbertSchmidtKernelPairing,
    realL2ExternalTensor_add_left, inner_add_right]

/-- The Hilbert--Schmidt kernel pairing is real-linear in the left test vector. -/
theorem realL2HilbertSchmidtKernelPairing_smul_left
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing K (c • f) g =
      c • realL2HilbertSchmidtKernelPairing K f g := by
  simp [realL2HilbertSchmidtKernelPairing,
    realL2ExternalTensor_smul_left, real_inner_smul_right]

/-- The Hilbert--Schmidt kernel pairing is additive in the right test vector. -/
theorem realL2HilbertSchmidtKernelPairing_add_right
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g₁ g₂ : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing K f (g₁ + g₂) =
      realL2HilbertSchmidtKernelPairing K f g₁ +
        realL2HilbertSchmidtKernelPairing K f g₂ := by
  simp [realL2HilbertSchmidtKernelPairing,
    realL2ExternalTensor_add_right, inner_add_right]

/-- The Hilbert--Schmidt kernel pairing is real-linear in the right test vector. -/
theorem realL2HilbertSchmidtKernelPairing_smul_right
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing K f (c • g) =
      c • realL2HilbertSchmidtKernelPairing K f g := by
  simp [realL2HilbertSchmidtKernelPairing,
    realL2ExternalTensor_smul_right, real_inner_smul_right]

/-- Sharp Hilbert--Schmidt/Cauchy--Schwarz bound for the kernel pairing. -/
theorem realL2HilbertSchmidtKernelPairing_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    ‖realL2HilbertSchmidtKernelPairing K f g‖ ≤
      ‖K‖ * ‖f‖ * ‖g‖ := by
  calc
    ‖realL2HilbertSchmidtKernelPairing K f g‖ =
        ‖inner ℝ K (realL2ExternalTensor f g)‖ := rfl
    _ ≤ ‖K‖ * ‖realL2ExternalTensor f g‖ :=
      norm_inner_le_norm K (realL2ExternalTensor f g)
    _ = ‖K‖ * (‖f‖ * ‖g‖) := by
      rw [realL2ExternalTensor_norm]
    _ = ‖K‖ * ‖f‖ * ‖g‖ := by ring

/-- The Hilbert--Schmidt kernel pairing is a bounded bilinear map.  The
`IsBoundedBilinearMap` witness uses the harmless positive constant `‖K‖+1`;
the sharp constant `‖K‖` is retained separately in
`realL2HilbertSchmidtKernelPairing_norm_le`. -/
theorem realL2HilbertSchmidtKernelPairing_isBoundedBilinearMap
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    IsBoundedBilinearMap ℝ
      (fun p : Lp ℝ 2 μ × Lp ℝ 2 ν =>
        realL2HilbertSchmidtKernelPairing K p.1 p.2) := by
  refine
    { add_left := ?_
      smul_left := ?_
      add_right := ?_
      smul_right := ?_
      bound := ?_ }
  · intro f₁ f₂ g
    exact realL2HilbertSchmidtKernelPairing_add_left K f₁ f₂ g
  · intro c f g
    exact realL2HilbertSchmidtKernelPairing_smul_left K c f g
  · intro f g₁ g₂
    exact realL2HilbertSchmidtKernelPairing_add_right K f g₁ g₂
  · intro c f g
    exact realL2HilbertSchmidtKernelPairing_smul_right K c f g
  · refine ⟨‖K‖ + 1, by positivity, ?_⟩
    intro f g
    calc
      ‖realL2HilbertSchmidtKernelPairing K f g‖ ≤
          ‖K‖ * ‖f‖ * ‖g‖ :=
        realL2HilbertSchmidtKernelPairing_norm_le K f g
      _ ≤ (‖K‖ + 1) * ‖f‖ * ‖g‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f))
          (norm_nonneg g)

/-- The bundled continuous bilinear Hilbert--Schmidt form associated with a
real product-`L²` kernel. -/
noncomputable def realL2HilbertSchmidtKernelBilinear
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν →L[ℝ] ℝ :=
  (realL2HilbertSchmidtKernelPairing_isBoundedBilinearMap K).toContinuousLinearMap

/-- The bundled bilinear form evaluates to the original kernel/external-tensor
inner product. -/
@[simp] theorem realL2HilbertSchmidtKernelBilinear_apply
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    (realL2HilbertSchmidtKernelBilinear K f) g =
      realL2HilbertSchmidtKernelPairing K f g := by
  rfl

/-- For fixed left vector, the resulting continuous functional has operator
norm at most `‖K‖ ‖f‖`. -/
theorem realL2HilbertSchmidtKernelBilinear_apply_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) :
    ‖realL2HilbertSchmidtKernelBilinear K f‖ ≤ ‖K‖ * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (realL2HilbertSchmidtKernelBilinear K f)
    (mul_nonneg (norm_nonneg K) (norm_nonneg f))
  intro g
  simpa [mul_assoc] using
    realL2HilbertSchmidtKernelPairing_norm_le K f g

/-- The operator norm of the complete bundled bilinear map is bounded by the
Hilbert--Schmidt `L²` norm of its kernel. -/
theorem realL2HilbertSchmidtKernelBilinear_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ‖realL2HilbertSchmidtKernelBilinear K‖ ≤ ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (realL2HilbertSchmidtKernelBilinear K)
    (norm_nonneg K)
  intro f
  exact realL2HilbertSchmidtKernelBilinear_apply_norm_le K f

/-- Audit-visible generic Hilbert--Schmidt kernel bilinear package. -/
structure RealL2HilbertSchmidtKernelBilinearPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) : Prop where
  sharpPairingBound :
    ∀ (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν),
      ‖realL2HilbertSchmidtKernelPairing K f g‖ ≤
        ‖K‖ * ‖f‖ * ‖g‖
  bundledNormBound :
    ‖realL2HilbertSchmidtKernelBilinear K‖ ≤ ‖K‖

/-- Construct the complete generic Hilbert--Schmidt bilinear receipt. -/
theorem realL2HilbertSchmidtKernelBilinearPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    RealL2HilbertSchmidtKernelBilinearPackage K :=
  { sharpPairingBound := realL2HilbertSchmidtKernelPairing_norm_le K
    bundledNormBound := realL2HilbertSchmidtKernelBilinear_norm_le K }

end

end MathlibAnalytic
end MGAP4D
