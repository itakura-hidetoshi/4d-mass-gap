import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralLogHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    IsStrictlyPositive (D.vacuumOrthogonalComplexSpectralTransferOperator n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_isStrictlyPositive D n

example :
    D.vacuumOrthogonalComplexSpectralTransferOperator n ≤
      algebraMap ℝ
        (D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        (Real.exp (-exactGapValueReal)) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_le_exactGap_exp D n

example :
    IsSelfAdjoint (D.vacuumOrthogonalComplexSpectralLogHamiltonian n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_isSelfAdjoint D n

example :
    NormedSpace.exp (-D.vacuumOrthogonalComplexSpectralLogHamiltonian n) =
      D.vacuumOrthogonalComplexSpectralTransferOperator n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_exp_neg_logHamiltonian D n

example :
    algebraMap ℝ
        (D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        exactGapValueReal ≤
      D.vacuumOrthogonalComplexSpectralLogHamiltonian n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_exactGap_le_logHamiltonian D n

example :
    0 ≤ D.vacuumOrthogonalComplexSpectralLogHamiltonian n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_nonneg D n

example :
    (D.vacuumOrthogonalComplexSpectralLogHamiltonian n).IsPositive :=
  finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_isPositive D n

end

end MathlibAnalytic
end MGAP4D
