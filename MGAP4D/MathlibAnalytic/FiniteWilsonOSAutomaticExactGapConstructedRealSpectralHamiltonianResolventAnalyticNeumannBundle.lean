import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventAnalyticNeumannBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventFactorialDerivativeBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The exact distance-to-gap ball makes the constructed finite Wilson
resolvent perturbation strictly contractive. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖(mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ < 1 := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- Exact local inverse representation of the constructed finite Wilson
resolvent under the normalized contraction condition. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_eq_inverse_one_sub_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal)
    (hsmall :
      ‖(mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ < 1) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
      Ring.inverse
          (1 - (mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hmu hsmall)

/-- Exact local inverse representation of the constructed finite Wilson
resolvent on the full distance-to-gap ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
      Ring.inverse
          (1 - (mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- Exact finite ordered Neumann expansion with remainder for the constructed
finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
      (∑ i ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ i) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda +
      ((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ N *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda hdist)

/-- Real analyticity of the constructed finite Wilson resolvent at every
parameter strictly below the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_analyticAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    AnalyticAt ℝ
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_analyticAt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Neighborhood real analyticity of the constructed finite Wilson resolvent
throughout the exact sub-gap interval. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_analyticOnNhd
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    AnalyticOnNhd ℝ
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_analyticOnNhd
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- Within-set real analyticity of the constructed finite Wilson resolvent
throughout the exact sub-gap interval. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_analyticOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    AnalyticOn ℝ
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_analyticOn
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- Analyticity, exact local inverse representation, and finite ordered Neumann
expansions for the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventAnalyticNeumann_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    AnalyticOnNhd ℝ
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      AnalyticOn ℝ
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      ∀ {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
          (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda),
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
            Ring.inverse
                (1 - (mu - lambda) •
                  finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) *
              finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda ∧
          ∀ N : ℕ,
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
              (∑ i ∈ Finset.range N,
                  ((mu - lambda) •
                    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ i) *
                finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda +
              ((mu - lambda) •
                  finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ N *
                finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolventAnalyticNeumann_package
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

end MathlibAnalytic
end MGAP4D

end
