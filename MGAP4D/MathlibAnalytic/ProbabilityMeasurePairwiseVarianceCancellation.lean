import MGAP4D.MathlibAnalytic.RealL2ConditionalIndependentPairVariance
import Mathlib.Tactic

/-!
# Exact factor-two cancellation for pairwise variance bounds

Suppose a real L2 observable M on a probability space satisfies a pairwise
difference estimate

  (M u - M v)^2 <= c^2 * (V u + V v)

for an integrable real profile V.  Integrating over two independent copies
produces exactly

  E[(M(U)-M(V))^2] <= 2 c^2 E[V].

The independent-pair identity gives

  E[(M(U)-M(V))^2] = 2 Var(M),

so the same factor two occurs on both sides and cancels:

  Var(M) <= c^2 E[V].

This is the normalization needed after the cross-boundary L2 mean-difference
estimate.  No triangle inequality, cardinality factor, or hidden factor two is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Integrating a pointwise pairwise square-difference estimate over two
independent copies produces exactly the expected factor two on the profile
side. -/
theorem realProbabilityIndependentPair_integral_sq_sub_le_two_mul_coeff_sq_mul_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (M V : α → ℝ)
    (hM : MemLp M 2 μ)
    (hV : Integrable V μ)
    (c : ℝ)
    (hpair : ∀ u v,
      (M u - M v) ^ 2 ≤ c ^ 2 * (V u + V v)) :
    (∫ uv : α × α, (M uv.1 - M uv.2) ^ 2 ∂μ.prod μ) ≤
      2 * c ^ 2 * ∫ u, V u ∂μ := by
  let D : α × α → ℝ := fun z => M z.1 - M z.2
  have hD : MemLp D 2 (μ.prod μ) := by
    dsimp [D]
    exact (hM.comp_fst μ).sub (hM.comp_snd μ)
  have hLeftInt : Integrable (fun z => (D z) ^ 2) (μ.prod μ) := by
    simpa only [Pi.pow_apply] using hD.integrable_sq
  have hVFst : Integrable (fun z : α × α => V z.1) (μ.prod μ) :=
    hV.comp_fst μ
  have hVSnd : Integrable (fun z : α × α => V z.2) (μ.prod μ) :=
    hV.comp_snd μ
  have hRightInt :
      Integrable (fun z : α × α => c ^ 2 * (V z.1 + V z.2)) (μ.prod μ) :=
    (hVFst.add hVSnd).const_mul (c ^ 2)
  calc
    (∫ uv : α × α, (M uv.1 - M uv.2) ^ 2 ∂μ.prod μ) =
        ∫ z, (D z) ^ 2 ∂μ.prod μ := by rfl
    _ ≤ ∫ z, c ^ 2 * (V z.1 + V z.2) ∂μ.prod μ := by
      refine integral_mono_ae hLeftInt hRightInt ?_
      exact Filter.Eventually.of_forall fun z => hpair z.1 z.2
    _ = 2 * c ^ 2 * ∫ u, V u ∂μ := by
      rw [integral_const_mul,
        integral_add hVFst hVSnd,
        integral_fun_fst, integral_fun_snd]
      simp
      ring

/-- Exact independent-pair variance identity in real-integral form. -/
theorem realProbabilityIndependentPair_integral_sq_sub_eq_two_mul_variance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (M : α → ℝ)
    (hM : MemLp M 2 μ) :
    (∫ uv : α × α, (M uv.1 - M uv.2) ^ 2 ∂μ.prod μ) =
      2 * variance M μ := by
  let D : α × α → ℝ := fun z => M z.1 - M z.2
  have hD : MemLp D 2 (μ.prod μ) := by
    dsimp [D]
    exact (hM.comp_fst μ).sub (hM.comp_snd μ)
  have hMInt : Integrable M μ := hM.integrable one_le_two
  have hMeanZero : ∫ z, D z ∂(μ.prod μ) = 0 := by
    dsimp [D]
    rw [integral_sub (hMInt.comp_fst μ) (hMInt.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  have hVarianceIntegral :
      variance D (μ.prod μ) = ∫ z, (D z) ^ 2 ∂(μ.prod μ) :=
    variance_of_integral_eq_zero hD.aemeasurable hMeanZero
  have hVarianceProd :=
    variance_add_prod (μ := μ) (ν := μ) hM hM.neg
  calc
    (∫ uv : α × α, (M uv.1 - M uv.2) ^ 2 ∂μ.prod μ) =
        ∫ z, (D z) ^ 2 ∂μ.prod μ := by rfl
    _ = variance D (μ.prod μ) := hVarianceIntegral.symm
    _ = variance M μ + variance (fun u => -M u) μ := by
      simpa [D, sub_eq_add_neg] using hVarianceProd
    _ = 2 * variance M μ := by
      rw [variance_fun_neg]
      ring

/-- Pairwise variance-sensitive estimates descend to a one-copy variance
estimate with no extra factor two. -/
theorem realProbability_variance_le_coeff_sq_mul_integral_of_pairwise_sq_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (M V : α → ℝ)
    (hM : MemLp M 2 μ)
    (hV : Integrable V μ)
    (c : ℝ)
    (hpair : ∀ u v,
      (M u - M v) ^ 2 ≤ c ^ 2 * (V u + V v)) :
    variance M μ ≤ c ^ 2 * ∫ u, V u ∂μ := by
  have hUpper :=
    realProbabilityIndependentPair_integral_sq_sub_le_two_mul_coeff_sq_mul_integral
      μ M V hM hV c hpair
  have hExact :=
    realProbabilityIndependentPair_integral_sq_sub_eq_two_mul_variance
      μ M hM
  rw [hExact] at hUpper
  linarith

end

end MGAP4D.MathlibAnalytic
