import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalTransferOperatorInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    IsUnit (D.vacuumOrthogonalTransferOperator n) :=
  finite_wilson_vacuum_orthogonal_transfer_operator_isUnit D n

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalTransferOperator n *
        D.vacuumOrthogonalTransferOperatorInverse n = 1 :=
  finite_wilson_vacuum_orthogonal_transfer_operator_mul_inverse D n

example
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalTransferOperatorInverse n *
        D.vacuumOrthogonalTransferOperator n = 1 :=
  finite_wilson_vacuum_orthogonal_transfer_operator_inverse_mul D n

example
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
  finite_wilson_vacuum_orthogonal_transfer_operator_inverse_on_eigenbasis D n i

end

end MathlibAnalytic
end MGAP4D
