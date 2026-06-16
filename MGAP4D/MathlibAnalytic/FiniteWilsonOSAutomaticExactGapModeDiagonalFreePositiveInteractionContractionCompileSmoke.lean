import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)

noncomputable def finite_wilson_mode_diagonal_free_positive_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W :=
  D.toFreePositiveInteractionData

theorem finite_wilson_mode_diagonal_free_coercive_compile_smoke
    (n : ℕ) (x : D.StateSpace) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (D.freeHamiltonian n x) x :=
  finite_wilson_mode_diagonal_free_hamiltonian_coercive D n x

theorem finite_wilson_mode_diagonal_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin D.StateDimension) :
    exactGapValueReal ≤
      (finite_wilson_free_positive_total_hamiltonian_symmetric
        D.toFreePositiveInteractionData n).eigenvalues D.stateFinrank i :=
  finite_wilson_mode_diagonal_total_hamiltonian_eigenvalues_ge_exactGap D n i

theorem finite_wilson_mode_diagonal_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_mode_diagonal_free_positive_interaction_continuum_bound
    D O r

end

end MathlibAnalytic
end MGAP4D
