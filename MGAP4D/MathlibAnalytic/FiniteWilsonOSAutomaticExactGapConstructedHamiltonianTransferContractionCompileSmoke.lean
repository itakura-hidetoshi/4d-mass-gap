import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContractionData W)

noncomputable def finite_wilson_constructed_hamiltonian_eigenaction_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W :=
  D.toHamiltonianEigenactionData

theorem finite_wilson_constructed_hamiltonian_eigenaction_compile_smoke
    (n : ℕ) (i : Fin D.StateDimension) :
    D.transferOperator n
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) =
      Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) •
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) :=
  finite_wilson_constructed_hamiltonian_transfer_on_eigenbasis D n i

theorem finite_wilson_constructed_hamiltonian_operator_bound_compile_smoke
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_constructed_hamiltonian_transfer D n

theorem finite_wilson_constructed_hamiltonian_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_constructed_hamiltonian_transfer_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
