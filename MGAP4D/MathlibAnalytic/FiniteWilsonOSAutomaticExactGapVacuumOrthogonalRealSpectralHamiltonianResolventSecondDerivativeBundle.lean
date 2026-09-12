import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventSecondDerivativeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventDerivativeBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

/-- The first derivative of the finite Wilson `Ω⊥` resolvent has the ordered
cubic product-rule within-derivative. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv_hasDerivWithinAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivWithinAt
      (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n))
      (((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)).comp
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) +
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
          ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)))
      (Set.Iio exactGapValueReal) lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_hasDerivWithinAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- Ordinary second differentiability of the finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    HasDerivAt
      (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n))
      (((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)).comp
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) +
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
          ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)))
      lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_hasDerivAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- Explicit second derivative formula on the finite Wilson `Ω⊥` sector. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_secondDeriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    deriv (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)) lambda =
      ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)).comp
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) +
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
          ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_secondDeriv
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- The first derivative of the finite Wilson `Ω⊥` resolvent is differentiable
throughout the exact sub-gap interval. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv_differentiableOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    DifferentiableOn ℝ
      (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n))
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_differentiableOn
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The second derivative on the finite Wilson `Ω⊥` sector is continuous in
operator norm below the exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_continuousOn_secondDeriv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContinuousOn
      (deriv (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)))
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_continuousOn_secondDeriv
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The first derivative on the finite Wilson `Ω⊥` sector is `C¹`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_deriv_contDiffOn_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 1
      (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n))
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_deriv_contDiffOn_one
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The finite Wilson `Ω⊥` resolvent is `C²` in operator norm below the exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_contDiffOn_two
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 2
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_contDiffOn_two
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Exact reciprocal-cube bound for the finite Wilson `Ω⊥` second resolvent
derivative. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_secondDeriv_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ‖deriv (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)) lambda‖ ≤
      2 * (((exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹) *
          (exactGapValueReal - lambda)⁻¹) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_secondDeriv_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda

/-- Fixed-state reciprocal-cube control for the finite Wilson `Ω⊥` second
resolvent derivative. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_secondDeriv_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal)
    (x : D.gapData.ExcitedStateSpace) :
    ‖deriv (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)) lambda x‖ ≤
      (2 * (((exactGapValueReal - lambda)⁻¹ *
        (exactGapValueReal - lambda)⁻¹) *
          (exactGapValueReal - lambda)⁻¹)) * ‖x‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_secondDeriv_apply_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n hlambda x

/-- `C²`, exact second derivative formula, and reciprocal-cube control for the
finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventSecondDerivative_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiffOn ℝ 2
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      DifferentiableOn ℝ
        (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n))
        (Set.Iio exactGapValueReal) ∧
      ∀ {lambda : ℝ} (hlambda : lambda < exactGapValueReal),
        deriv (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)) lambda =
            ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
                (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)).comp
              (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) +
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
              ((finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda).comp
                (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)) ∧
          ‖deriv (deriv (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)) lambda‖ ≤
            2 * (((exactGapValueReal - lambda)⁻¹ *
              (exactGapValueReal - lambda)⁻¹) *
                (exactGapValueReal - lambda)⁻¹) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolventSecondDerivative_package
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

end MathlibAnalytic
end MGAP4D

end
