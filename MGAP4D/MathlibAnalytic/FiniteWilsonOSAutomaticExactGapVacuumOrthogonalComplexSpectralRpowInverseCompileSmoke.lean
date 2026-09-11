import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralRpowInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralTransferOperator n).IsPositive :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_isPositive D n

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    IsUnit (D.vacuumOrthogonalComplexSpectralTransferOperator n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_isUnit D n

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (-1) =
      D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_neg_one D n

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (-x) =
      ComplexContinuousPositiveContraction.rpow
        (D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n) x :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_neg D n x

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x y : ℝ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (x + y) =
      D.vacuumOrthogonalComplexSpectralTransferRpow n x *
        D.vacuumOrthogonalComplexSpectralTransferRpow n y :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_add D n x y

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n x *
        D.vacuumOrthogonalComplexSpectralTransferRpow n (-x) = 1 :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_mul_neg D n x

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (-1)
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      (Real.exp
          ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
            D.gapData n).eigenvalues D.gapData.excitedFinrank i) : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_neg_one_on_basis D n i

end

end MathlibAnalytic
end MGAP4D
