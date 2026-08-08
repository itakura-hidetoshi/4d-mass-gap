import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
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

/-- The squared Hilbert norm of a real `L²` vector is the integral of the
pointwise squared norm of any chosen representative. -/
theorem realL2_norm_sq_eq_integral_norm_sq
    (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := by
      simpa using (real_inner_self_eq_norm_sq f).symm
    _ = ∫ a, inner ℝ (f a) (f a) ∂μ :=
      MeasureTheory.L2.inner_def f f
    _ = ∫ a, ‖f a‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      exact real_inner_self_eq_norm_sq (f a)

/-- Pointwise external tensor product of two real `L²` representatives. -/
def realL2ExternalTensorFunction
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : α × β → ℝ :=
  fun z => f z.1 * g z.2

/-- The external tensor product of two real `L²` vectors belongs to
`L²(μ × ν)`.  This is the product-measure square-integrability fact needed by
Hilbert--Schmidt kernel pairings. -/
theorem realL2ExternalTensorFunction_memLp_two
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    MemLp (realL2ExternalTensorFunction f g) 2 (μ.prod ν) := by
  have hfMeas : AEStronglyMeasurable (fun a => f a) μ :=
    Lp.aestronglyMeasurable f
  have hgMeas : AEStronglyMeasurable (fun b => g b) ν :=
    Lp.aestronglyMeasurable g
  have hMeas : AEStronglyMeasurable (realL2ExternalTensorFunction f g) (μ.prod ν) := by
    exact hfMeas.comp_fst.mul hgMeas.comp_snd
  have hfSq : Integrable (fun a => ‖f a‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hfMeas).1 (Lp.memLp f)
  have hgSq : Integrable (fun b => ‖g b‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hgMeas).1 (Lp.memLp g)
  have hSq : Integrable
      (fun z : α × β => ‖realL2ExternalTensorFunction f g z‖ ^ 2)
      (μ.prod ν) := by
    simpa [realL2ExternalTensorFunction, norm_mul, mul_pow] using
      hfSq.mul_prod hgSq
  exact (memLp_two_iff_integrable_sq_norm hMeas).2 hSq

/-- Canonical external tensor product as a vector of `L²(μ × ν)`. -/
noncomputable def realL2ExternalTensor
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (realL2ExternalTensorFunction_memLp_two f g).toLp
    (realL2ExternalTensorFunction f g)

/-- The canonical `L²` external tensor is represented almost everywhere by
ordinary pointwise multiplication of the two pulled-back representatives. -/
theorem realL2ExternalTensor_coeFn
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensor f g =ᵐ[μ.prod ν]
      realL2ExternalTensorFunction f g :=
  (realL2ExternalTensorFunction_memLp_two f g).coeFn_toLp

/-- Exact Hilbert cross-norm identity for the real `L²` external tensor. -/
theorem realL2ExternalTensor_norm_sq
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    ‖realL2ExternalTensor f g‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  rw [realL2_norm_sq_eq_integral_norm_sq]
  calc
    (∫ z, ‖realL2ExternalTensor f g z‖ ^ 2 ∂(μ.prod ν)) =
        ∫ z : α × β, ‖f z.1‖ ^ 2 * ‖g z.2‖ ^ 2 ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards [realL2ExternalTensor_coeFn f g] with z hz
      rw [hz]
      simp [realL2ExternalTensorFunction, norm_mul, mul_pow]
    _ = (∫ a, ‖f a‖ ^ 2 ∂μ) * ∫ b, ‖g b‖ ^ 2 ∂ν := by
      exact integral_prod_mul
        (fun a => ‖f a‖ ^ 2) (fun b => ‖g b‖ ^ 2)
    _ = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
      rw [← realL2_norm_sq_eq_integral_norm_sq f,
        ← realL2_norm_sq_eq_integral_norm_sq g]

/-- Exact multiplicative norm of the real `L²` external tensor. -/
theorem realL2ExternalTensor_norm
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    ‖realL2ExternalTensor f g‖ = ‖f‖ * ‖g‖ := by
  have hsq := realL2ExternalTensor_norm_sq f g
  have hsq' :
      ‖realL2ExternalTensor f g‖ ^ 2 = (‖f‖ * ‖g‖) ^ 2 := by
    calc
      ‖realL2ExternalTensor f g‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 := hsq
      _ = (‖f‖ * ‖g‖) ^ 2 := by ring
  have hleft : 0 ≤ ‖realL2ExternalTensor f g‖ := norm_nonneg _
  have hright : 0 ≤ ‖f‖ * ‖g‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- External tensor is additive in the left factor. -/
theorem realL2ExternalTensor_add_left
    [SFinite μ] [SFinite ν]
    (f₁ f₂ : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensor (f₁ + f₂) g =
      realL2ExternalTensor f₁ g + realL2ExternalTensor f₂ g := by
  apply Lp.ext
  filter_upwards [realL2ExternalTensor_coeFn (f₁ + f₂) g,
    realL2ExternalTensor_coeFn f₁ g,
    realL2ExternalTensor_coeFn f₂ g,
    Lp.coeFn_add f₁ f₂,
    Lp.coeFn_add (realL2ExternalTensor f₁ g) (realL2ExternalTensor f₂ g)] with z h h1 h2 hf hadd
  simp only [realL2ExternalTensorFunction] at h h1 h2
  rw [h, h1, h2, hf, hadd]
  ring

/-- External tensor is additive in the right factor. -/
theorem realL2ExternalTensor_add_right
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g₁ g₂ : Lp ℝ 2 ν) :
    realL2ExternalTensor f (g₁ + g₂) =
      realL2ExternalTensor f g₁ + realL2ExternalTensor f g₂ := by
  apply Lp.ext
  filter_upwards [realL2ExternalTensor_coeFn f (g₁ + g₂),
    realL2ExternalTensor_coeFn f g₁,
    realL2ExternalTensor_coeFn f g₂,
    Lp.coeFn_add g₁ g₂,
    Lp.coeFn_add (realL2ExternalTensor f g₁) (realL2ExternalTensor f g₂)] with z h h1 h2 hg hadd
  simp only [realL2ExternalTensorFunction] at h h1 h2
  rw [h, h1, h2, hg, hadd]
  ring

/-- External tensor is real-linear in the left factor. -/
theorem realL2ExternalTensor_smul_left
    [SFinite μ] [SFinite ν]
    (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensor (c • f) g = c • realL2ExternalTensor f g := by
  apply Lp.ext
  filter_upwards [realL2ExternalTensor_coeFn (c • f) g,
    realL2ExternalTensor_coeFn f g,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c (realL2ExternalTensor f g)] with z h hfg hf hsmul
  simp only [realL2ExternalTensorFunction] at h hfg
  rw [h, hfg, hf, hsmul]
  simp [smul_eq_mul]

/-- External tensor is real-linear in the right factor. -/
theorem realL2ExternalTensor_smul_right
    [SFinite μ] [SFinite ν]
    (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensor f (c • g) = c • realL2ExternalTensor f g := by
  apply Lp.ext
  filter_upwards [realL2ExternalTensor_coeFn f (c • g),
    realL2ExternalTensor_coeFn f g,
    Lp.coeFn_smul c g,
    Lp.coeFn_smul c (realL2ExternalTensor f g)] with z h hfg hg hsmul
  simp only [realL2ExternalTensorFunction] at h hfg
  rw [h, hfg, hg, hsmul]
  simp [smul_eq_mul]

/-- Audit-visible exact cross-norm receipt for the real `L²` external tensor. -/
structure RealL2ExternalTensorPackage
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : Prop where
  memLpTwo : MemLp (realL2ExternalTensorFunction f g) 2 (μ.prod ν)
  normEq : ‖realL2ExternalTensor f g‖ = ‖f‖ * ‖g‖

/-- The canonical external tensor construction supplies the complete exact
cross-norm receipt. -/
theorem realL2ExternalTensorPackage
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    RealL2ExternalTensorPackage f g :=
  { memLpTwo := realL2ExternalTensorFunction_memLp_two f g
    normEq := realL2ExternalTensor_norm f g }

end

end MathlibAnalytic
end MGAP4D
