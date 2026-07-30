import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventDerivativeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventIdentityContinuityBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

/-- The finite Wilson `Ω⊥` resolvent is continuous in operator norm on the open
exact sub-gap interval. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_continuousOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContinuousOn
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_continuousOn
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The within-derivative of the finite Wilson `Ω⊥` resolvent is its operator
square. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_hasDerivWithinAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivWithinAt
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda))
      (Set.Iio exactGapValueReal) lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_hasDerivWithinAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- The ordinary operator-norm derivative of the finite Wilson `Ω⊥` resolvent is
its square. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivAt
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda))
      lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_hasDerivAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- Explicit derivative formula for the finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n) lambda =
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- The finite Wilson `Ω⊥` resolvent is differentiable throughout the open exact
sub-gap interval. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_differentiableOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    DifferentiableOn ℝ
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_differentiableOn
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The derivative of the finite Wilson `Ω⊥` resolvent is continuous in operator
norm below the exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_continuousOn_deriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContinuousOn
      (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n))
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_continuousOn_deriv
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The finite Wilson `Ω⊥` resolvent is `C¹` in operator norm below the exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_contDiffOn_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 1
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_contDiffOn_one
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Exact reciprocal-square distance-to-gap bound for the finite Wilson `Ω⊥`
resolvent derivative. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
      (exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- Fixed-state reciprocal-square derivative control for the finite Wilson
`Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal)
    (x : D.gapData.ExcitedStateSpace) :
    ‖deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n) lambda x‖ ≤
      ((exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹) * ‖x‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_apply_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda x

/-- `C¹`, exact derivative formula, and reciprocal-square derivative control for
the finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventDerivative_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 1
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      DifferentiableOn ℝ
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < exactGapValueReal),
        deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n) lambda =
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
              (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ∧
          ‖deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n) lambda‖ ≤
            (exactGapValueReal - lambda)⁻¹ *
              (exactGapValueReal - lambda)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolventDerivative_package
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

end MathlibAnalytic
end MGAP4D

end
