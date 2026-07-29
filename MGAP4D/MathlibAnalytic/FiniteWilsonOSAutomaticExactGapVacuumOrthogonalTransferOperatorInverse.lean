import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedTransferOperatorInverse
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact-gap transfer operator acting on the physical excitation sector
`Ω⊥`, obtained from vacuum-orthogonal Hamiltonian coercivity. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalTransferOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.transferOperator n

/-- The explicit inverse transfer operator on the physical excitation sector
`Ω⊥`. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalTransferOperatorInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.transferOperatorInverse n

/-- The vacuum-orthogonal transfer operator followed by its explicit inverse is
the identity on `Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_transfer_operator_mul_inverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalTransferOperator n *
        D.vacuumOrthogonalTransferOperatorInverse n = 1 :=
  finite_wilson_constructed_transfer_operator_mul_inverse
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The explicit inverse followed by the vacuum-orthogonal transfer operator is
the identity on `Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_transfer_operator_inverse_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalTransferOperatorInverse n *
        D.vacuumOrthogonalTransferOperator n = 1 :=
  finite_wilson_constructed_transfer_operator_inverse_mul
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Vacuum-orthogonal Hamiltonian coercivity therefore produces an invertible
finite-volume transfer operator on the physical excitation sector, with no
positive lower bound imposed on the vacuum line. -/
theorem finite_wilson_vacuum_orthogonal_transfer_operator_isUnit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    IsUnit (D.vacuumOrthogonalTransferOperator n) :=
  finite_wilson_constructed_transfer_operator_isUnit
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- On each excitation Hamiltonian eigenmode, the inverse transfer operator acts
by `exp(Eᵢ)`. -/
theorem finite_wilson_vacuum_orthogonal_transfer_operator_inverse_on_eigenbasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalTransferOperatorInverse n
        ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
          D.gapData n).eigenvectorBasis D.gapData.excitedFinrank i) =
      Real.exp
          ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
            D.gapData n).eigenvalues D.gapData.excitedFinrank i) •
        ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
          D.gapData n).eigenvectorBasis D.gapData.excitedFinrank i) :=
  finite_wilson_constructed_transfer_operator_inverse_on_eigenbasis
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n i

end

end MathlibAnalytic
end MGAP4D
