import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v w

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- A Hilbert--Schmidt kernel pairing factors through a real Hilbert feature
operator when it is exactly the Hilbert inner product of the two analyzed
vectors.  This is the quotient-level `A* A` interface; no pointwise
representative of the output operator is chosen. -/
def RealL2HilbertSchmidtKernelPairingGramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Lp ℝ 2 μ →L[ℝ] H) : Prop :=
  ∀ f g : Lp ℝ 2 μ,
    realL2HilbertSchmidtKernelPairing K f g = inner ℝ (A f) (A g)

/-- An exact Gram factorization makes the kernel pairing symmetric. -/
theorem realL2HilbertSchmidtKernelPairing_symmetric_of_gramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) :
    RealL2HilbertSchmidtKernelPairingSymmetric K := by
  intro f g
  rw [hGram f g, hGram g f]
  exact real_inner_comm _ _

/-- An exact Gram factorization makes every pairing quadratic form
nonnegative. -/
theorem realL2HilbertSchmidtKernelPairing_nonnegative_of_gramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) :
    RealL2HilbertSchmidtKernelPairingNonnegative K := by
  intro f
  rw [hGram f f]
  exact real_inner_self_nonneg

/-- The quadratic form of the associated Fréchet--Riesz operator is exactly the
squared Hilbert norm of the analyzed feature vector. -/
theorem realL2HilbertSchmidtKernelOperator_inner_self_eq_norm_sq_of_gramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A)
    (f : Lp ℝ 2 μ) :
    inner ℝ (realL2HilbertSchmidtKernelOperator K f) f = ‖A f‖ ^ 2 := by
  rw [realL2HilbertSchmidtKernelOperator_inner K f f, hGram f f]
  exact real_inner_self_eq_norm_sq _

/-- A Hilbert--Schmidt kernel with an exact Gram factorization produces a
positive bounded operator. -/
theorem realL2HilbertSchmidtKernelOperator_isPositive_of_gramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) :
    ((realL2HilbertSchmidtKernelOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsPositive := by
  exact realL2HilbertSchmidtKernelOperator_isPositive K
    (realL2HilbertSchmidtKernelPairing_symmetric_of_gramFactorization
      K H A hGram)
    (realL2HilbertSchmidtKernelPairing_nonnegative_of_gramFactorization
      K H A hGram)

/-- A representative-level real Gram kernel is the integral of products of a
shared feature over an auxiliary measure. -/
def RealL2KernelRepresentativeIntegralGram
    {β : Type w} [MeasurableSpace β]
    (ν : Measure β)
    (k : α × α → ℝ)
    (φ : α × β → ℝ) : Prop :=
  ∀ p : α × α,
    k p = ∫ x, φ (p.1, x) * φ (p.2, x) ∂ν

/-- Mathlib's real scalar inner product is ordinary multiplication.  The proof
uses only Hilbert-space identities and is robust against scalar-inner simp
normal forms. -/
theorem realL2Scalar_inner_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  have h11 : inner ℝ (1 : ℝ) (1 : ℝ) = 1 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (1 : ℝ))
  calc
    inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
    _ = a * inner ℝ (1 : ℝ) (b • (1 : ℝ)) := by
      rw [real_inner_smul_left]
    _ = a * (b * inner ℝ (1 : ℝ) (1 : ℝ)) := by
      rw [real_inner_smul_right]
    _ = a * b := by
      rw [h11]
      ring

/-- Generic scalar Fubini bridge for a Gram-represented square kernel.

The only analytic hypothesis exposed here is integrability of the natural
three-variable weighted Gram product for the chosen `L²` vector.  Under that
hypothesis the complete kernel quadratic form is exactly an integral of
squares. -/
theorem realL2HilbertSchmidtKernelPairing_self_eq_integral_sq_of_ae_integralGram_rep
    {β : Type w} [MeasurableSpace β]
    [SFinite μ] {ν : Measure β} [SFinite ν]
    (K : Lp ℝ 2 (μ.prod μ))
    (k : α × α → ℝ)
    (φ : α × β → ℝ)
    (hK : (fun p => K p) =ᵐ[μ.prod μ] k)
    (hGram : RealL2KernelRepresentativeIntegralGram ν k φ)
    (f : Lp ℝ 2 μ)
    (hIntegrable : Integrable
      (fun q : (α × α) × β =>
        (φ (q.1.1, q.2) * f q.1.1) *
          (φ (q.1.2, q.2) * f q.1.2))
      ((μ.prod μ).prod ν)) :
    realL2HilbertSchmidtKernelPairing K f f =
      ∫ x : β, (∫ b : α, φ (b, x) * f b ∂μ) ^ 2 ∂ν := by
  have hff := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f f
  let F : α × α → β → ℝ := fun p x =>
    (φ (p.1, x) * f p.1) * (φ (p.2, x) * f p.2)
  have hFIntegrable : Integrable (Function.uncurry F) ((μ.prod μ).prod ν) := by
    simpa [F, Function.uncurry] using hIntegrable
  calc
    realL2HilbertSchmidtKernelPairing K f f =
        ∫ p : α × α, k p * (f p.1 * f p.2) ∂(μ.prod μ) := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hK, hff] with p hpK hpff
      rw [hpK, hpff]
      simp [realL2ExternalTensorFunction, realL2Scalar_inner_eq_mul]
    _ = ∫ p : α × α, ∫ x : β, F p x ∂ν ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hGram p]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      simp [F]
      ring
    _ = ∫ x : β, ∫ p : α × α, F p x ∂(μ.prod μ) ∂ν :=
      MeasureTheory.integral_integral_swap hFIntegrable
    _ = ∫ x : β, (∫ b : α, φ (b, x) * f b ∂μ) ^ 2 ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show (∫ p : α × α, F p x ∂(μ.prod μ)) =
          (∫ b : α, φ (b, x) * f b ∂μ) *
            (∫ c : α, φ (c, x) * f c ∂μ) by
        simpa [F] using
          (MeasureTheory.integral_prod_mul
            (μ := μ) (ν := μ)
            (fun b : α => φ (b, x) * f b)
            (fun c : α => φ (c, x) * f c))]
      ring

/-- Integral-of-squares realization implies complete `L²` quadratic
nonnegativity. -/
theorem realL2HilbertSchmidtKernelPairing_nonnegative_of_ae_integralGram_rep
    {β : Type w} [MeasurableSpace β]
    [SFinite μ] {ν : Measure β} [SFinite ν]
    (K : Lp ℝ 2 (μ.prod μ))
    (k : α × α → ℝ)
    (φ : α × β → ℝ)
    (hK : (fun p => K p) =ᵐ[μ.prod μ] k)
    (hGram : RealL2KernelRepresentativeIntegralGram ν k φ)
    (hIntegrable : ∀ f : Lp ℝ 2 μ, Integrable
      (fun q : (α × α) × β =>
        (φ (q.1.1, q.2) * f q.1.1) *
          (φ (q.1.2, q.2) * f q.1.2))
      ((μ.prod μ).prod ν)) :
    RealL2HilbertSchmidtKernelPairingNonnegative K := by
  intro f
  rw [realL2HilbertSchmidtKernelPairing_self_eq_integral_sq_of_ae_integralGram_rep
    K k φ hK hGram f (hIntegrable f)]
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)

end

end MathlibAnalytic
end MGAP4D
