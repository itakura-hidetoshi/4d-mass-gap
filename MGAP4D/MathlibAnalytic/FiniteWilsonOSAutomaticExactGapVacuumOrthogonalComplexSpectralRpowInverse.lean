import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralRpowInverse
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalTransferOperatorInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- The complex spectral realization of the physical excitation sector `Ω⊥`. -/
abbrev
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralStateSpace
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W) :
    Type :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralStateSpace

/-- The complex orthonormal spectral basis indexed by the real excitation
Hamiltonian modes. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralBasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W) :
    OrthonormalBasis (Fin D.gapData.ExcitedDimension) ℂ
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralBasis

/-- The complex spectral transfer operator generated from vacuum-orthogonal
Hamiltonian coercivity. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralTransferOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralTransferOperator n

/-- The explicit inverse of the complex spectral excitation transfer operator. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralTransferOperatorInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralTransferOperatorInverse n

/-- The unital CFC real power family on the complex spectral excitation space. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralTransferRpow
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralTransferRpow n x

/-- Vacuum-orthogonal coercivity generates a positive complex spectral transfer
operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralTransferOperator n).IsPositive :=
  finite_wilson_constructed_complex_spectral_transfer_isPositive
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The explicit complex spectral inverse is positive. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_inverse_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    (D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n).IsPositive :=
  finite_wilson_constructed_complex_spectral_transfer_inverse_isPositive
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The complex spectral excitation transfer operator followed by its inverse is
the identity. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_mul_inverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralTransferOperator n *
        D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n = 1 :=
  finite_wilson_constructed_complex_spectral_transfer_mul_inverse
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The inverse followed by the complex spectral excitation transfer operator is
the identity. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_inverse_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n *
        D.vacuumOrthogonalComplexSpectralTransferOperator n = 1 :=
  finite_wilson_constructed_complex_spectral_transfer_inverse_mul
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The complex spectral excitation transfer operator is invertible. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_isUnit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    IsUnit (D.vacuumOrthogonalComplexSpectralTransferOperator n) :=
  finite_wilson_constructed_complex_spectral_transfer_isUnit
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- On the complex spectral excitation space, CFC exponent `-1` is the explicit
inverse transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_neg_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (-1) =
      D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n :=
  finite_wilson_constructed_complex_spectral_transfer_rpow_neg_one
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Every negative real CFC power is the matching positive power of the explicit
inverse. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_neg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (-x) =
      ComplexContinuousPositiveContraction.rpow
        (D.vacuumOrthogonalComplexSpectralTransferOperatorInverse n) x :=
  finite_wilson_constructed_complex_spectral_transfer_rpow_neg
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- The excitation-sector CFC powers obey the full real-exponent addition law. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_add
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x y : ℝ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (x + y) =
      D.vacuumOrthogonalComplexSpectralTransferRpow n x *
        D.vacuumOrthogonalComplexSpectralTransferRpow n y :=
  finite_wilson_constructed_complex_spectral_transfer_rpow_add
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x y

/-- Opposite excitation-sector CFC powers multiply to the identity. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_mul_neg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n x *
        D.vacuumOrthogonalComplexSpectralTransferRpow n (-x) = 1 :=
  finite_wilson_constructed_complex_spectral_transfer_rpow_mul_neg
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- The complex spectral transfer operator acts on mode `i` with the same
coefficient `exp (-Eᵢ)` as the real vacuum-orthogonal transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralTransferOperator n
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      (Real.exp
          (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
            D.gapData n).eigenvalues D.gapData.excitedFinrank i)) : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_constructed_complex_spectral_transfer_on_basis
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n i

/-- CFC exponent `-1` acts on excitation mode `i` by `exp (Eᵢ)`. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_transfer_rpow_neg_one_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralTransferRpow n (-1)
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      (Real.exp
          ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
            D.gapData n).eigenvalues D.gapData.excitedFinrank i) : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_constructed_complex_spectral_transfer_rpow_neg_one_on_basis
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n i

end

end MathlibAnalytic
end MGAP4D
