import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W)

noncomputable def finite_wilson_hamiltonian_eigenaction_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W :=
  D.toFiniteDimensionalHamiltonianData

theorem finite_wilson_hamiltonian_eigenaction_rayleigh_compile_smoke
    (n : ℕ) (x : D.StateSpace) :
    inner ℝ (D.transferOperator n x) x =
      ∑ i : Fin D.StateDimension,
        (inner ℝ
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) x) ^ 2 *
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) :=
  finite_wilson_hamiltonian_eigenaction_rayleigh_representation D n x

theorem finite_wilson_hamiltonian_eigenaction_operator_bound_compile_smoke
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_hamiltonian_eigenaction D n

theorem finite_wilson_hamiltonian_eigenaction_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_hamiltonian_eigenaction_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
