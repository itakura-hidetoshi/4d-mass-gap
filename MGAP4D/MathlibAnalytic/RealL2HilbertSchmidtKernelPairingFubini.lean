import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelBilinear
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

/-- A real Hilbert--Schmidt kernel pairing can be evaluated by Fubini on any
chosen almost-everywhere representatives of the kernel and the two `L²` test
vectors.  Integrability of the displayed product integrand is automatic from
the `L²` hypotheses via Mathlib's `L2.integrable_inner`; no separate `L¹`
assumption is required. -/
theorem realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ)
    (g : Lp ℝ 2 ν)
    (κ : α × β → ℝ)
    (φ : α → ℝ)
    (γ : β → ℝ)
    (hK : K =ᵐ[μ.prod ν] κ)
    (hf : f =ᵐ[μ] φ)
    (hg : g =ᵐ[ν] γ) :
    realL2HilbertSchmidtKernelPairing K f g =
      ∫ y, ∫ x, inner ℝ (κ (x, y)) (φ x * γ y) ∂μ ∂ν := by
  let T := realL2ExternalTensor f g
  have hfprod :
      (fun z : α × β => f z.1) =ᵐ[μ.prod ν]
        (fun z => φ z.1) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq hf
  have hgprod :
      (fun z : α × β => g z.2) =ᵐ[μ.prod ν]
        (fun z => γ z.2) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq hg
  have hT :
      T =ᵐ[μ.prod ν] realL2ExternalTensorFunction f g := by
    simpa [T] using realL2ExternalTensor_coeFn f g
  have hrep :
      (fun z : α × β => inner ℝ (K z) (T z)) =ᵐ[μ.prod ν]
        (fun z => inner ℝ (κ z) (φ z.1 * γ z.2)) := by
    filter_upwards [hK, hT, hfprod, hgprod] with z hKz hTz hfz hgz
    rw [hKz, hTz]
    unfold realL2ExternalTensorFunction
    rw [hfz, hgz]
  have hinner :
      Integrable (fun z : α × β => inner ℝ (K z) (T z)) (μ.prod ν) :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℝ) K T
  have hdisplay :
      Integrable
        (fun z : α × β => inner ℝ (κ z) (φ z.1 * γ z.2))
        (μ.prod ν) :=
    hinner.congr hrep
  unfold realL2HilbertSchmidtKernelPairing
  change inner ℝ K T = _
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ z, inner ℝ (K z) (T z) ∂(μ.prod ν)) =
        ∫ z, inner ℝ (κ z) (φ z.1 * γ z.2) ∂(μ.prod ν) :=
      integral_congr_ae hrep
    _ = ∫ y, ∫ x, inner ℝ (κ (x, y)) (φ x * γ y) ∂μ ∂ν :=
      MeasureTheory.integral_prod_symm _ hdisplay

end

end MathlibAnalytic
end MGAP4D
