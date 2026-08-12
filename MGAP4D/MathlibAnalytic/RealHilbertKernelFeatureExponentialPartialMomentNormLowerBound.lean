import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureNonnegSMulMomentStrictness
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The right weighted moment of an `L²` direct-sum feature has norm at most
that of the full weighted moment.  This is the quantitative form of the
cancellation-free right-coordinate separation used by finite Fock sums. -/
theorem RealHilbertKernelFeature.add_weighted_integral_right_norm_le
    {X : Type} [MeasurableSpace X]
    {kernel₁ kernel₂ : X → X → ℝ}
    (C₁ : RealHilbertKernelFeature X kernel₁)
    (C₂ : RealHilbertKernelFeature X kernel₂)
    (μ : Measure X)
    (a : X → ℝ)
    (hIntegrable :
      Integrable
        (fun x => a x • (RealHilbertKernelFeature.add C₁ C₂).feature x) μ) :
    ‖∫ x, a x • C₂.feature x ∂μ‖ ≤
      ‖∫ x, a x • (RealHilbertKernelFeature.add C₁ C₂).feature x ∂μ‖ := by
  let M :=
    ∫ x, a x • (RealHilbertKernelFeature.add C₁ C₂).feature x ∂μ
  have hproj :=
    (WithLp.sndL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert).integral_comp_comm hIntegrable
  have hEq :
      (∫ x, a x • C₂.feature x ∂μ) =
        (WithLp.sndL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert) M := by
    simpa [M, RealHilbertKernelFeature.add] using hproj
  rw [hEq]
  simpa [M, WithLp.sndL] using (WithLp.norm_snd_le M)

/-- The left weighted moment of an `L²` direct-sum feature has norm at most
that of the full weighted moment. -/
theorem RealHilbertKernelFeature.add_weighted_integral_left_norm_le
    {X : Type} [MeasurableSpace X]
    {kernel₁ kernel₂ : X → X → ℝ}
    (C₁ : RealHilbertKernelFeature X kernel₁)
    (C₂ : RealHilbertKernelFeature X kernel₂)
    (μ : Measure X)
    (a : X → ℝ)
    (hIntegrable :
      Integrable
        (fun x => a x • (RealHilbertKernelFeature.add C₁ C₂).feature x) μ) :
    ‖∫ x, a x • C₁.feature x ∂μ‖ ≤
      ‖∫ x, a x • (RealHilbertKernelFeature.add C₁ C₂).feature x ∂μ‖ := by
  let M :=
    ∫ x, a x • (RealHilbertKernelFeature.add C₁ C₂).feature x ∂μ
  have hproj :=
    (WithLp.fstL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert).integral_comp_comm hIntegrable
  have hEq :
      (∫ x, a x • C₁.feature x ∂μ) =
        (WithLp.fstL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert) M := by
    simpa [M, RealHilbertKernelFeature.add] using hproj
  rw [hEq]
  simpa [M, WithLp.fstL] using (WithLp.norm_fst_le M)

/-- Adding the next nonnegative Taylor/Fock degree cannot decrease the norm of
the weighted moment of the previous finite exponential truncation. -/
theorem RealHilbertKernelFeature.exponentialPartial_weighted_integral_norm_le_succ
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (n : ℕ)
    (hIntegrable :
      Integrable
        (fun x => a x •
          (RealHilbertKernelFeature.exponentialPartial C c hc (n + 1)).feature x) μ) :
    ‖∫ x, a x •
        (RealHilbertKernelFeature.exponentialPartial C c hc n).feature x ∂μ‖ ≤
      ‖∫ x, a x •
        (RealHilbertKernelFeature.exponentialPartial C c hc (n + 1)).feature x ∂μ‖ := by
  have hCoefficient :
      0 ≤ c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    exact div_nonneg (pow_nonneg hc _) (by positivity)
  have hIntegrableAdd :
      Integrable
        (fun x => a x •
          (RealHilbertKernelFeature.add
            (RealHilbertKernelFeature.exponentialPartial C c hc n)
            (RealHilbertKernelFeature.nonnegSMul
              (c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
              hCoefficient
              (RealHilbertKernelFeature.pow C (n + 1)))).feature x) μ := by
    simpa [RealHilbertKernelFeature.exponentialPartial,
      RealHilbertKernelFeature.exponentialPartialKernel] using hIntegrable
  have h :=
    RealHilbertKernelFeature.add_weighted_integral_left_norm_le
      (RealHilbertKernelFeature.exponentialPartial C c hc n)
      (RealHilbertKernelFeature.nonnegSMul
        (c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
        hCoefficient
        (RealHilbertKernelFeature.pow C (n + 1)))
      μ a hIntegrableAdd
  simpa [RealHilbertKernelFeature.exponentialPartial,
    RealHilbertKernelFeature.exponentialPartialKernel] using h

/-- The newly inserted top Taylor/Fock degree gives a quantitative lower bound
for the norm of the whole successor truncation moment.  Hence a nonzero chosen
degree is not merely separated algebraically: its norm is protected inside the
finite direct sum. -/
theorem RealHilbertKernelFeature.exponentialPartial_top_weighted_integral_norm_le_succ
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (n : ℕ)
    (hIntegrable :
      Integrable
        (fun x => a x •
          (RealHilbertKernelFeature.exponentialPartial C c hc (n + 1)).feature x) μ) :
    ‖Real.sqrt (c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) •
        (∫ x, a x • (RealHilbertKernelFeature.pow C (n + 1)).feature x ∂μ)‖ ≤
      ‖∫ x, a x •
        (RealHilbertKernelFeature.exponentialPartial C c hc (n + 1)).feature x ∂μ‖ := by
  have hCoefficient :
      0 ≤ c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
    exact div_nonneg (pow_nonneg hc _) (by positivity)
  have hIntegrableAdd :
      Integrable
        (fun x => a x •
          (RealHilbertKernelFeature.add
            (RealHilbertKernelFeature.exponentialPartial C c hc n)
            (RealHilbertKernelFeature.nonnegSMul
              (c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
              hCoefficient
              (RealHilbertKernelFeature.pow C (n + 1)))).feature x) μ := by
    simpa [RealHilbertKernelFeature.exponentialPartial,
      RealHilbertKernelFeature.exponentialPartialKernel] using hIntegrable
  have h :=
    RealHilbertKernelFeature.add_weighted_integral_right_norm_le
      (RealHilbertKernelFeature.exponentialPartial C c hc n)
      (RealHilbertKernelFeature.nonnegSMul
        (c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
        hCoefficient
        (RealHilbertKernelFeature.pow C (n + 1)))
      μ a hIntegrableAdd
  rw [RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul] at h
  simpa [RealHilbertKernelFeature.exponentialPartial,
    RealHilbertKernelFeature.exponentialPartialKernel] using h

end

end MathlibAnalytic
end MGAP4D