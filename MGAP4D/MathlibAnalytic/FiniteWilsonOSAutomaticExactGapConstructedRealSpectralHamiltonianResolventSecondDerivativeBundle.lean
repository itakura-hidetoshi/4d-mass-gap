import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventSecondDerivativeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventDerivativeBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

/-- The first derivative of the constructed finite Wilson resolvent has the
within-derivative given by the ordered cubic product-rule sum. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_hasDerivWithinAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivWithinAt
      (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n))
      (((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)).comp
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) +
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
          ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)))
      (Set.Iio exactGapValueReal) lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivWithinAt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Ordinary second differentiability of the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivAt
      (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n))
      (((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)).comp
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) +
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
          ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)))
      lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv_hasDerivAt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Explicit second derivative formula for the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_secondDeriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    deriv (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)) lambda =
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)).comp
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) +
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
          ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_secondDeriv
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- The first derivative of the constructed finite Wilson resolvent is
differentiable throughout the exact sub-gap interval. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_differentiableOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    DifferentiableOn ℝ
      (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n))
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv_differentiableOn
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- The second derivative of the constructed finite Wilson resolvent is
continuous in operator norm below the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_continuousOn_secondDeriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContinuousOn
      (deriv (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)))
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_continuousOn_secondDeriv
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- The first derivative of the constructed finite Wilson resolvent is `C¹`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_contDiffOn_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 1
      (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n))
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv_contDiffOn_one
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- The constructed finite Wilson resolvent is `C²` in operator norm below the
exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_contDiffOn_two
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 2
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_contDiffOn_two
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- Exact reciprocal-cube bound for the constructed finite Wilson second
resolvent derivative. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_secondDeriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖deriv (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)) lambda‖ ≤
      2 * (((exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹) *
          (exactGapValueReal - lambda)⁻¹) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_secondDeriv_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Fixed-state reciprocal-cube control for the constructed finite Wilson
second resolvent derivative. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_secondDeriv_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal)
    (x : D.StateSpace) :
    ‖deriv (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)) lambda x‖ ≤
      (2 * (((exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹) *
          (exactGapValueReal - lambda)⁻¹)) * ‖x‖ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_secondDeriv_apply_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda x)

/-- `C²`, exact second derivative formula, and reciprocal-cube control for the
constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventSecondDerivative_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 2
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      DifferentiableOn ℝ
        (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n))
        (Set.Iio exactGapValueReal) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < exactGapValueReal),
        deriv (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)) lambda =
            ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
                (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)).comp
              (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) +
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
              ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
                (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)) ∧
          ‖deriv (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)) lambda‖ ≤
            2 * (((exactGapValueReal - lambda)⁻¹ *
              (exactGapValueReal - lambda)⁻¹) *
                (exactGapValueReal - lambda)⁻¹) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolventSecondDerivative_package
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

end MathlibAnalytic
end MGAP4D

end
