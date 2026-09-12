import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralLogHamiltonian
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralRpowInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- The canonical CFC logarithmic Hamiltonian on the complex spectral
realization of the physical excitation sector `Ω⊥`. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralLogHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralLogHamiltonian n

/-- The vacuum-orthogonal complex spectral transfer operator is strictly positive. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_isStrictlyPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    IsStrictlyPositive (D.vacuumOrthogonalComplexSpectralTransferOperator n) :=
  finite_wilson_constructed_complex_spectral_transfer_isStrictlyPositive
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal transfer operator satisfies the scalar exact-gap
upper bound. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_le_exactGap_exp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralTransferOperator n ≤
      algebraMap ℝ
        (D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        (Real.exp (-exactGapValueReal)) :=
  finite_wilson_constructed_complex_spectral_transfer_le_exactGap_exp
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal complex spectral logarithmic Hamiltonian is
self-adjoint. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_isSelfAdjoint
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    IsSelfAdjoint (D.vacuumOrthogonalComplexSpectralLogHamiltonian n) :=
  finite_wilson_constructed_complex_spectral_logHamiltonian_isSelfAdjoint
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Exponentiating the negative vacuum-orthogonal logarithmic Hamiltonian
recovers the complex spectral excitation transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_exp_neg_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    NormedSpace.exp (-D.vacuumOrthogonalComplexSpectralLogHamiltonian n) =
      D.vacuumOrthogonalComplexSpectralTransferOperator n :=
  finite_wilson_constructed_complex_spectral_exp_neg_logHamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The canonical vacuum-orthogonal logarithmic Hamiltonian has the exact-gap
operator lower bound. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_exactGap_le_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    algebraMap ℝ
        (D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        exactGapValueReal ≤
      D.vacuumOrthogonalComplexSpectralLogHamiltonian n :=
  finite_wilson_constructed_complex_spectral_exactGap_le_logHamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal logarithmic Hamiltonian is nonnegative. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_nonneg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    0 ≤ D.vacuumOrthogonalComplexSpectralLogHamiltonian n :=
  finite_wilson_constructed_complex_spectral_logHamiltonian_nonneg
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal logarithmic Hamiltonian is positive in the bundled
continuous-linear-map sense. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralLogHamiltonian n).IsPositive :=
  finite_wilson_constructed_complex_spectral_logHamiltonian_isPositive
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

end

end MathlibAnalytic
end MGAP4D
