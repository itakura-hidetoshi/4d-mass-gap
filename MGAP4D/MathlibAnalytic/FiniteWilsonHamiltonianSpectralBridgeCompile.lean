import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)

noncomputable def finite_wilson_hamiltonian_bridge_compile :
    FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W :=
  D.toOrthonormalEigenbasisData

theorem finite_wilson_hamiltonian_eigenvector_compile
    (n : ℕ) (i : Fin D.StateDimension) :
    D.hamiltonian n
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) =
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i •
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) :=
  finite_wilson_finite_dimensional_hamiltonian_apply_eigenbasis D n i

theorem finite_wilson_hamiltonian_operator_bound_compile (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_finite_dimensional_hamiltonian D n

end

end MathlibAnalytic
end MGAP4D
