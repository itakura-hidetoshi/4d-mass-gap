import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Variance of one bounded continuous observable in an approximating physical
Yang--Mills probability measure. -/
def PhysicalFourDimensionalYangMillsWeakLimit.approximatingObservableVariance
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (n : ℕ)
    (O : BoundedContinuousFunction S.Configuration ℝ) : ℝ :=
  (∫ A, (O * O) A ∂(S.approximatingMeasure n : Measure S.Configuration)) -
    (∫ A, O A ∂(S.approximatingMeasure n : Measure S.Configuration)) ^ 2

/-- Variance of one bounded continuous observable in the continuum physical
Yang--Mills probability measure. -/
def PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ) : ℝ :=
  (∫ A, (O * O) A ∂(S.continuumMeasure : Measure S.Configuration)) -
    (∫ A, O A ∂(S.continuumMeasure : Measure S.Configuration)) ^ 2

/-- Weak convergence transports the variance of every bounded continuous
physical observable. -/
theorem physical_yang_mills_bounded_observable_variance_converges
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ => S.approximatingObservableVariance n O)
      atTop
      (nhds (S.continuumObservableVariance O)) := by
  unfold
    PhysicalFourDimensionalYangMillsWeakLimit.approximatingObservableVariance
    PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance
  exact
    (physical_yang_mills_bounded_observable_expectation_converges S (O * O)).sub
      ((physical_yang_mills_bounded_observable_expectation_converges S O).pow 2)

/-- A uniform finite-scale lower bound for one observable variance passes to the
continuum weak limit. -/
theorem physical_yang_mills_continuumObservableVariance_ge_of_uniform_approximating_ge
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ)
    (c : ℝ)
    (hLower : ∀ n, c ≤ S.approximatingObservableVariance n O) :
    c ≤ S.continuumObservableVariance O := by
  exact
    le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
      (physical_yang_mills_bounded_observable_variance_converges S O)
      (Eventually.of_forall hLower)

/-- Positive continuum variance excludes almost-everywhere equality of the
observable with any constant. -/
theorem physical_yang_mills_continuumObservable_not_ae_eq_const_of_variance_pos
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ)
    (hVariancePos : 0 < S.continuumObservableVariance O)
    (c : ℝ) :
    ¬ (fun A : S.Configuration => O A) =ᵐ[
        (S.continuumMeasure : Measure S.Configuration)]
      (fun _ => c) := by
  intro hConst
  have hMean :
      (∫ A, O A ∂(S.continuumMeasure : Measure S.Configuration)) = c := by
    calc
      (∫ A, O A ∂(S.continuumMeasure : Measure S.Configuration)) =
          ∫ _A : S.Configuration, c
            ∂(S.continuumMeasure : Measure S.Configuration) :=
        integral_congr_ae hConst
      _ = c := by simp
  have hSquareConst :
      (fun A : S.Configuration => (O * O) A) =ᵐ[
          (S.continuumMeasure : Measure S.Configuration)]
        (fun _ => c * c) := by
    filter_upwards [hConst] with A hA
    simp [hA]
  have hSecond :
      (∫ A, (O * O) A
          ∂(S.continuumMeasure : Measure S.Configuration)) = c * c := by
    calc
      (∫ A, (O * O) A
          ∂(S.continuumMeasure : Measure S.Configuration)) =
          ∫ _A : S.Configuration, c * c
            ∂(S.continuumMeasure : Measure S.Configuration) :=
        integral_congr_ae hSquareConst
      _ = c * c := by simp
  have hVarianceZero : S.continuumObservableVariance O = 0 := by
    unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance
    rw [hMean, hSecond]
    ring
  linarith

/-- A concrete nontriviality input for a physical weak limit: one bounded
continuous observable has a scale-uniform strictly positive variance. -/
structure PhysicalFourDimensionalYangMillsWeakLimit.ObservableNontrivialityCertificate
    (S : PhysicalFourDimensionalYangMillsWeakLimit) where
  observable : BoundedContinuousFunction S.Configuration ℝ
  lowerBound : ℝ
  lowerBound_pos : 0 < lowerBound
  approximating_variance_ge :
    ∀ n, lowerBound ≤ S.approximatingObservableVariance n observable

/-- An observable nontriviality certificate produces strictly positive
continuum variance. -/
theorem PhysicalFourDimensionalYangMillsWeakLimit.ObservableNontrivialityCertificate.continuum_variance_pos
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    (C : S.ObservableNontrivialityCertificate) :
    0 < S.continuumObservableVariance C.observable := by
  exact lt_of_lt_of_le C.lowerBound_pos
    (physical_yang_mills_continuumObservableVariance_ge_of_uniform_approximating_ge
      S C.observable C.lowerBound C.approximating_variance_ge)

/-- The certified continuum observable cannot collapse almost everywhere to
any constant. -/
theorem PhysicalFourDimensionalYangMillsWeakLimit.ObservableNontrivialityCertificate.observable_not_ae_eq_const
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    (C : S.ObservableNontrivialityCertificate)
    (c : ℝ) :
    ¬ (fun A : S.Configuration => C.observable A) =ᵐ[
        (S.continuumMeasure : Measure S.Configuration)]
      (fun _ => c) :=
  physical_yang_mills_continuumObservable_not_ae_eq_const_of_variance_pos
    S C.observable C.continuum_variance_pos c

end

end MathlibAnalytic
end MGAP4D
