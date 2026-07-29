import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionRpowInverse
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedTransferOperatorInverse
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- A finite-dimensional complex spectral realization of the constructed
exact-gap excitation space.  It has one complex coordinate for each real
Hamiltonian eigenmode. -/
abbrev
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralStateSpace
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) : Type :=
  EuclideanSpace ℂ (Fin D.StateDimension)

/-- A chosen complex orthonormal basis indexed by the real Hamiltonian modes. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralBasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) :
    OrthonormalBasis (Fin D.StateDimension) ℂ D.complexSpectralStateSpace :=
  (stdOrthonormalBasis ℂ D.complexSpectralStateSpace).reindex
    (finCongr (by
      simp [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralStateSpace]))

/-- The complex spectral transfer operator with the same mode coefficients
`exp (-Eᵢ)` as the constructed real transfer operator. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) : D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace :=
  orthonormalComplexDiagonalOperator D.complexSpectralBasis
    (fun i =>
      Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))

/-- The explicit complex spectral inverse, with coefficients `exp (Eᵢ)`. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperatorInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) : D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace :=
  orthonormalComplexDiagonalOperator D.complexSpectralBasis
    (fun i =>
      (Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))⁻¹)

/-- The unital CFC real power of the complex spectral transfer operator. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferRpow
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) : D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace :=
  ComplexContinuousPositiveContraction.rpow
    (D.complexSpectralTransferOperator n) x

/-- The complex spectral transfer operator is positive. -/
theorem finite_wilson_constructed_complex_spectral_transfer_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralTransferOperator n).IsPositive := by
  apply orthonormalComplexDiagonalOperator_isPositive
  intro i
  exact (Real.exp_pos _).le

/-- The explicit complex spectral inverse is positive. -/
theorem finite_wilson_constructed_complex_spectral_transfer_inverse_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralTransferOperatorInverse n).IsPositive := by
  apply orthonormalComplexDiagonalOperator_isPositive
  intro i
  exact (inv_pos.mpr (Real.exp_pos _)).le

/-- The complex spectral transfer operator followed by its explicit inverse is
the identity. -/
theorem finite_wilson_constructed_complex_spectral_transfer_mul_inverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralTransferOperator n *
        D.complexSpectralTransferOperatorInverse n = 1 := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator,
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperatorInverse]
    using
      orthonormalComplexDiagonalOperator_mul_inv D.complexSpectralBasis
        (fun i =>
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
        (fun i => Real.exp_ne_zero _)

/-- The explicit inverse followed by the complex spectral transfer operator is
the identity. -/
theorem finite_wilson_constructed_complex_spectral_transfer_inverse_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralTransferOperatorInverse n *
        D.complexSpectralTransferOperator n = 1 := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator,
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperatorInverse]
    using
      orthonormalComplexDiagonalOperator_inv_mul D.complexSpectralBasis
        (fun i =>
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
        (fun i => Real.exp_ne_zero _)

/-- The complex spectral transfer operator is a unit. -/
theorem finite_wilson_constructed_complex_spectral_transfer_isUnit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    IsUnit (D.complexSpectralTransferOperator n) := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator]
    using
      orthonormalComplexDiagonalOperator_isUnit D.complexSpectralBasis
        (fun i =>
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
        (fun i => Real.exp_ne_zero _)

/-- CFC exponent `-1` is the explicit complex spectral inverse. -/
theorem finite_wilson_constructed_complex_spectral_transfer_rpow_neg_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralTransferRpow n (-1) =
      D.complexSpectralTransferOperatorInverse n := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferRpow
  exact ComplexContinuousPositiveContraction.rpow_neg_one_eq_explicitInverse
    (D.complexSpectralTransferOperator n)
    (D.complexSpectralTransferOperatorInverse n)
    (finite_wilson_constructed_complex_spectral_transfer_isPositive D n)
    (finite_wilson_constructed_complex_spectral_transfer_mul_inverse D n)
    (finite_wilson_constructed_complex_spectral_transfer_inverse_mul D n)

/-- Every negative real power is the corresponding positive power of the
explicit inverse. -/
theorem finite_wilson_constructed_complex_spectral_transfer_rpow_neg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.complexSpectralTransferRpow n (-x) =
      ComplexContinuousPositiveContraction.rpow
        (D.complexSpectralTransferOperatorInverse n) x := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferRpow
  exact ComplexContinuousPositiveContraction.rpow_neg_eq_explicitInverse_rpow
    (D.complexSpectralTransferOperator n)
    (D.complexSpectralTransferOperatorInverse n)
    x
    (finite_wilson_constructed_complex_spectral_transfer_isPositive D n)
    (finite_wilson_constructed_complex_spectral_transfer_mul_inverse D n)
    (finite_wilson_constructed_complex_spectral_transfer_inverse_mul D n)

/-- In the invertible complex spectral realization, the CFC real powers satisfy
the full addition law for arbitrary real exponents. -/
theorem finite_wilson_constructed_complex_spectral_transfer_rpow_add
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x y : ℝ) :
    D.complexSpectralTransferRpow n (x + y) =
      D.complexSpectralTransferRpow n x *
        D.complexSpectralTransferRpow n y := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferRpow
  exact ComplexContinuousPositiveContraction.rpow_add_of_isUnit
    (D.complexSpectralTransferOperator n) x y
    (finite_wilson_constructed_complex_spectral_transfer_isUnit D n)

/-- Opposite CFC powers multiply to the identity. -/
theorem finite_wilson_constructed_complex_spectral_transfer_rpow_mul_neg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : ℝ) :
    D.complexSpectralTransferRpow n x *
        D.complexSpectralTransferRpow n (-x) = 1 := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferRpow
  exact ComplexContinuousPositiveContraction.rpow_mul_rpow_neg_of_isUnit
    (D.complexSpectralTransferOperator n) x
    (finite_wilson_constructed_complex_spectral_transfer_isPositive D n)
    (finite_wilson_constructed_complex_spectral_transfer_isUnit D n)

/-- The complex spectral transfer operator has the same `exp (-Eᵢ)` mode
coefficient as the real constructed transfer operator. -/
theorem finite_wilson_constructed_complex_spectral_transfer_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.StateDimension) :
    D.complexSpectralTransferOperator n (D.complexSpectralBasis i) =
      (Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) : ℂ) •
        D.complexSpectralBasis i := by
  exact orthonormalComplexDiagonalOperator_apply_basis _ _ i

/-- On each complex spectral mode, the explicit inverse acts by `exp (Eᵢ)`. -/
theorem finite_wilson_constructed_complex_spectral_transfer_inverse_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.StateDimension) :
    D.complexSpectralTransferOperatorInverse n (D.complexSpectralBasis i) =
      (Real.exp ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i) : ℂ) •
        D.complexSpectralBasis i := by
  rw [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperatorInverse,
    orthonormalComplexDiagonalOperator_apply_basis]
  rw [Real.exp_neg]
  simp

/-- The CFC power at `-1` acts by `exp (Eᵢ)` on every complex spectral mode. -/
theorem finite_wilson_constructed_complex_spectral_transfer_rpow_neg_one_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.StateDimension) :
    D.complexSpectralTransferRpow n (-1) (D.complexSpectralBasis i) =
      (Real.exp ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i) : ℂ) •
        D.complexSpectralBasis i := by
  rw [finite_wilson_constructed_complex_spectral_transfer_rpow_neg_one D n]
  exact finite_wilson_constructed_complex_spectral_transfer_inverse_on_basis D n i

end

end MathlibAnalytic
end MGAP4D
