import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventFactorialDerivativeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventSecondDerivativeBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

/-- The `k`-th power of the constructed finite Wilson resolvent has derivative
`k • R^(k+1)` below the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_pow_hasDerivWithinAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivWithinAt
      (fun mu =>
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu) ^ k)
      ((k : ℝ) •
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^
          (k + 1))
      (Set.Iio exactGapValueReal) lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_pow_hasDerivWithinAt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) k hlambda)

/-- The constructed finite Wilson resolvent is `Cᵏ` in operator norm for every
finite order below the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_contDiffOn_nat
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) :
    ContDiffOn ℝ k
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_contDiffOn_nat
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) k)

/-- The constructed finite Wilson resolvent is smooth in operator norm below
the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_contDiffOn_infty
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ ∞
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_contDiffOn_infty
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- Finite-order and smooth regularity package for the constructed finite
Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventSmoothness_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ ∞
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      ∀ k : ℕ,
        ContDiffOn ℝ k
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
          (Set.Iio exactGapValueReal) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolventSmoothness_package
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

/-- Exact within-interval all-order derivative formula for the constructed
finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_iteratedDerivWithin
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    iteratedDerivWithin k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) lambda =
      (k.factorial : ℝ) •
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^
          (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_iteratedDerivWithin
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) k hlambda)

/-- Exact ordinary all-order derivative formula for the constructed finite
Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_iteratedDeriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda =
      (k.factorial : ℝ) •
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^
          (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_iteratedDeriv
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) k hlambda)

/-- Exact factorial distance-to-gap operator-norm bound for every derivative of
the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_iteratedDeriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
      (k.factorial : ℝ) *
        ((exactGapValueReal - lambda)⁻¹) ^ (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) k hlambda)

/-- Uniform factorial derivative control on every fixed truncation below the
exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_iteratedDeriv_norm_le_of_le_sub
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {epsilon lambda : ℝ} (hepsilon : 0 < epsilon)
    (hlambda : lambda < exactGapValueReal)
    (haway : lambda ≤ exactGapValueReal - epsilon) :
    ‖iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
      (k.factorial : ℝ) * (epsilon⁻¹) ^ (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le_of_le_sub
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      k hepsilon hlambda haway)

/-- Fixed-state factorial derivative control for the constructed finite Wilson
resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_iteratedDeriv_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal)
    (x : D.StateSpace) :
    ‖(iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda) x‖ ≤
      ((k.factorial : ℝ) *
        ((exactGapValueReal - lambda)⁻¹) ^ (k + 1)) * ‖x‖ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_apply_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) k hlambda x)

/-- Smoothness, exact all-order derivatives, and factorial operator-norm bounds
for the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventFactorialDerivative_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ ∞
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      (∀ (k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal),
        iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda =
          (k.factorial : ℝ) •
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^
              (k + 1)) ∧
      ∀ (k : ℕ) {lambda : ℝ} (_ : lambda < exactGapValueReal),
        ‖iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
          (k.factorial : ℝ) *
            ((exactGapValueReal - lambda)⁻¹) ^ (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolventFactorialDerivative_package
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n))

end MathlibAnalytic
end MGAP4D

end
