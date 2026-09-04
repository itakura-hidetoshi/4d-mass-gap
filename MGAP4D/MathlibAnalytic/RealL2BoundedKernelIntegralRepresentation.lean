import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- Fiberwise integral output of a bounded real kernel on a probability space.
This is the literal integral-operator representative that underlies the
Fréchet--Riesz Hilbert--Schmidt construction. -/
noncomputable def realL2BoundedKernelIntegralOutput
    (k : α → α → ℝ)
    (f : Lp ℝ 2 μ)
    (y : α) : ℝ :=
  ∫ x, k x y * f x ∂μ

/-- A jointly a.e.-strongly-measurable kernel gives an a.e.-strongly-measurable
fiber integral. -/
theorem realL2BoundedKernelIntegralOutput_aestronglyMeasurable
    [SFinite μ]
    (k : α → α → ℝ)
    (hkMeas : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (μ.prod μ))
    (f : Lp ℝ 2 μ) :
    AEStronglyMeasurable (realL2BoundedKernelIntegralOutput (μ := μ) k f) μ := by
  have hjoint :
      AEStronglyMeasurable
        (fun p : α × α => k p.1 p.2 * f p.1)
        (μ.prod μ) :=
    hkMeas.mul (Lp.aestronglyMeasurable f).comp_fst
  simpa [realL2BoundedKernelIntegralOutput] using hjoint.integral_prod_left'

/-- On a probability space, a jointly measurable kernel bounded in absolute
value by one sends every real `L²` representative to an `L²` fiber-integral
representative. -/
theorem realL2BoundedKernelIntegralOutput_memLp_two
    [SFinite μ]
    [IsProbabilityMeasure μ]
    (k : α → α → ℝ)
    (hkMeas : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (μ.prod μ))
    (hkBound : ∀ x y, |k x y| ≤ 1)
    (f : Lp ℝ 2 μ) :
    MemLp (realL2BoundedKernelIntegralOutput (μ := μ) k f) 2 μ := by
  have hfInt : Integrable (fun x => f x) μ :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hmeas :=
    realL2BoundedKernelIntegralOutput_aestronglyMeasurable
      (μ := μ) k hkMeas f
  let C : ℝ := ∫ x, ‖f x‖ ∂μ
  have hbound :
      ∀ y, ‖realL2BoundedKernelIntegralOutput (μ := μ) k f y‖ ≤ C := by
    intro y
    apply norm_integral_le_of_norm_le hfInt.norm
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs]
    have hk := hkBound x y
    nlinarith [norm_nonneg (f x), abs_nonneg (k x y)]
  have htop : MemLp (realL2BoundedKernelIntegralOutput (μ := μ) k f) ∞ μ :=
    memLp_top_of_bound hmeas C (Filter.Eventually.of_forall hbound)
  exact htop.mono_exponent (by norm_num)

/-- Canonical `L²` vector represented by the literal fiber integral. -/
noncomputable def realL2BoundedKernelIntegralOutputL2
    [SFinite μ]
    [IsProbabilityMeasure μ]
    (k : α → α → ℝ)
    (hkMeas : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (μ.prod μ))
    (hkBound : ∀ x y, |k x y| ≤ 1)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (realL2BoundedKernelIntegralOutput_memLp_two
    (μ := μ) k hkMeas hkBound f).toLp
      (realL2BoundedKernelIntegralOutput (μ := μ) k f)

/-- The canonical output `L²` vector has the literal fiber integral as an a.e.
representative. -/
theorem realL2BoundedKernelIntegralOutputL2_coeFn
    [SFinite μ]
    [IsProbabilityMeasure μ]
    (k : α → α → ℝ)
    (hkMeas : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (μ.prod μ))
    (hkBound : ∀ x y, |k x y| ≤ 1)
    (f : Lp ℝ 2 μ) :
    realL2BoundedKernelIntegralOutputL2 (μ := μ) k hkMeas hkBound f =ᵐ[μ]
      realL2BoundedKernelIntegralOutput (μ := μ) k f :=
  (realL2BoundedKernelIntegralOutput_memLp_two
    (μ := μ) k hkMeas hkBound f).coeFn_toLp

/-- Fubini identifies the Hilbert--Schmidt kernel pairing with the ordinary
fiber-integral output paired against an arbitrary right test vector. -/
theorem realL2BoundedKernelPairing_eq_integralOutput
    [SFinite μ]
    [IsProbabilityMeasure μ]
    (k : α → α → ℝ)
    (K : Lp ℝ 2 (μ.prod μ))
    (hK : K =ᵐ[μ.prod μ] fun p => k p.1 p.2)
    (f g : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelPairing K f g =
      ∫ y, realL2BoundedKernelIntegralOutput (μ := μ) k f y * g y ∂μ := by
  let E := realL2ExternalTensor f g
  have hE : E =ᵐ[μ.prod μ] realL2ExternalTensorFunction f g := by
    simpa [E] using realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f g
  have hprod : Integrable (fun p => K p * E p) (μ.prod μ) := by
    exact MemLp.integrable_mul (Lp.memLp K) (Lp.memLp E)
  have hraw :
      Integrable (fun p : α × α => k p.1 p.2 * (f p.1 * g p.2)) (μ.prod μ) := by
    apply hprod.congr
    filter_upwards [hK, hE] with p hk he
    rw [hk, he]
    rfl
  change inner ℝ K E = _
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ p, inner ℝ (K p) (E p) ∂(μ.prod μ)) =
        ∫ p : α × α, k p.1 p.2 * (f p.1 * g p.2) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [hK, hE] with p hk he
      rw [hk, he]
      simp [realL2ExternalTensorFunction, realL2Scalar_inner_eq_mul]
    _ = ∫ y, ∫ x, k x y * (f x * g y) ∂μ ∂μ := by
      exact integral_prod_symm _ hraw
    _ = ∫ y, realL2BoundedKernelIntegralOutput (μ := μ) k f y * g y ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      simp [realL2BoundedKernelIntegralOutput]
      ring

/-- For a bounded measurable raw representative of an `L²` kernel, the
Fréchet--Riesz Hilbert--Schmidt operator is exactly the `L²` class of the
literal fiber integral. -/
theorem realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
    [SFinite μ]
    [IsProbabilityMeasure μ]
    (k : α → α → ℝ)
    (K : Lp ℝ 2 (μ.prod μ))
    (hK : K =ᵐ[μ.prod μ] fun p => k p.1 p.2)
    (hkMeas : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (μ.prod μ))
    (hkBound : ∀ x y, |k x y| ≤ 1)
    (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelOperator K f =
      realL2BoundedKernelIntegralOutputL2 (μ := μ) k hkMeas hkBound f := by
  apply ext_inner_right ℝ
  intro g
  rw [realL2HilbertSchmidtKernelOperator_inner]
  rw [realL2BoundedKernelPairing_eq_integralOutput (μ := μ) k K hK f g]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    realL2BoundedKernelIntegralOutputL2_coeFn
      (μ := μ) k hkMeas hkBound f] with y hy
  rw [hy]
  simp [realL2Scalar_inner_eq_mul]

end

end MathlibAnalytic
end MGAP4D
