import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventDerivativeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventIdentityContinuityBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

/-- The constructed finite Wilson resolvent is continuous in operator norm on the
open exact sub-gap interval. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_continuousOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContinuousOn
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_continuousOn
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- The within-derivative of the constructed finite Wilson resolvent is its
operator square. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_hasDerivWithinAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivWithinAt
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda))
      (Set.Iio exactGapValueReal) lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_hasDerivWithinAt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- The ordinary operator-norm derivative of the constructed finite Wilson
resolvent is its square. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivAt
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda))
      lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_hasDerivAt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Explicit derivative formula for the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda =
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- The constructed finite Wilson resolvent is differentiable throughout the
open exact sub-gap interval. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_differentiableOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    DifferentiableOn ℝ
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_differentiableOn
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- The derivative of the constructed finite Wilson resolvent is continuous in
operator norm below the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_continuousOn_deriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContinuousOn
      (deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n))
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_continuousOn_deriv
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- The constructed finite Wilson resolvent is `C¹` in operator norm below the
exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_contDiffOn_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 1
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_contDiffOn_one
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- Exact reciprocal-square distance-to-gap bound for the constructed resolvent
derivative. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
      (exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Fixed-state reciprocal-square derivative control for the constructed
resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal)
    (x : D.StateSpace) :
    ‖deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda x‖ ≤
      ((exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹) * ‖x‖ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_deriv_apply_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hlambda x)

/-- `C¹`, exact derivative formula, and reciprocal-square derivative control for
the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventDerivative_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 1
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      DifferentiableOn ℝ
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < exactGapValueReal),
        deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda =
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda).comp
              (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ∧
          ‖deriv (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
            (exactGapValueReal - lambda)⁻¹ *
              (exactGapValueReal - lambda)⁻¹ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolventDerivative_package
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

end MathlibAnalytic
end MGAP4D

end
