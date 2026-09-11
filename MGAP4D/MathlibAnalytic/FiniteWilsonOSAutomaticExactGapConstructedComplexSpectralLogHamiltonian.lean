import MGAP4D.MathlibAnalytic.ComplexStrictlyPositiveLogHamiltonian
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralRpowInverse
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorOrder

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- The canonical CFC logarithmic Hamiltonian of the constructed complex
spectral transfer operator. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralLogHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace :=
  ComplexStrictlyPositiveOperator.logHamiltonian
    (D.complexSpectralTransferOperator n)

/-- The constructed complex spectral transfer operator is strictly positive. -/
theorem finite_wilson_constructed_complex_spectral_transfer_isStrictlyPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    IsStrictlyPositive (D.complexSpectralTransferOperator n) :=
  ComplexStrictlyPositiveOperator.isStrictlyPositive_of_isPositive_isUnit
    (D.complexSpectralTransferOperator n)
    (finite_wilson_constructed_complex_spectral_transfer_isPositive D n)
    (finite_wilson_constructed_complex_spectral_transfer_isUnit D n)

/-- The exact Hamiltonian eigenvalue lower bound gives the scalar transfer
upper bound `T ≤ exp (-δ) I`. -/
theorem finite_wilson_constructed_complex_spectral_transfer_le_exactGap_exp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralTransferOperator n ≤
      algebraMap ℝ
        (D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace)
        (Real.exp (-exactGapValueReal)) := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator
  rw [← orthonormalComplexDiagonalOperator_const_eq_algebraMap
    D.complexSpectralBasis (Real.exp (-exactGapValueReal))]
  apply orthonormalComplexDiagonalOperator_le
  intro i
  exact Real.exp_le_exp.mpr
    (neg_le_neg (D.hamiltonianEigenvalues_ge_exactGap n i))

/-- The constructed logarithmic Hamiltonian is self-adjoint. -/
theorem finite_wilson_constructed_complex_spectral_logHamiltonian_isSelfAdjoint
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    IsSelfAdjoint (D.complexSpectralLogHamiltonian n) :=
  ComplexStrictlyPositiveOperator.logHamiltonian_isSelfAdjoint
    (D.complexSpectralTransferOperator n)

/-- Exponentiating the negative logarithmic Hamiltonian recovers the complex
spectral transfer operator. -/
theorem finite_wilson_constructed_complex_spectral_exp_neg_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    NormedSpace.exp (-D.complexSpectralLogHamiltonian n) =
      D.complexSpectralTransferOperator n :=
  ComplexStrictlyPositiveOperator.exp_neg_logHamiltonian
    (D.complexSpectralTransferOperator n)
    (finite_wilson_constructed_complex_spectral_transfer_isStrictlyPositive D n)

/-- The CFC logarithmic Hamiltonian inherits the exact-gap lower bound. -/
theorem finite_wilson_constructed_complex_spectral_exactGap_le_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    algebraMap ℝ
        (D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace)
        exactGapValueReal ≤
      D.complexSpectralLogHamiltonian n :=
  ComplexStrictlyPositiveOperator.algebraMap_le_logHamiltonian_of_le_exp_neg_algebraMap
    (D.complexSpectralTransferOperator n)
    exactGapValueReal
    (finite_wilson_constructed_complex_spectral_transfer_isStrictlyPositive D n)
    (finite_wilson_constructed_complex_spectral_transfer_le_exactGap_exp D n)

/-- The constructed logarithmic Hamiltonian is nonnegative. -/
theorem finite_wilson_constructed_complex_spectral_logHamiltonian_nonneg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    0 ≤ D.complexSpectralLogHamiltonian n :=
  ComplexStrictlyPositiveOperator.logHamiltonian_nonneg_of_pos_lower_bound
    (D.complexSpectralTransferOperator n)
    exactGapValueReal
    exactGapValueReal_pos
    (finite_wilson_constructed_complex_spectral_exactGap_le_logHamiltonian D n)

/-- The constructed logarithmic Hamiltonian is positive in the bundled
continuous-linear-map sense. -/
theorem finite_wilson_constructed_complex_spectral_logHamiltonian_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralLogHamiltonian n).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive
    (D.complexSpectralLogHamiltonian n)).1
      (finite_wilson_constructed_complex_spectral_logHamiltonian_nonneg D n)

end

end MathlibAnalytic
end MGAP4D
