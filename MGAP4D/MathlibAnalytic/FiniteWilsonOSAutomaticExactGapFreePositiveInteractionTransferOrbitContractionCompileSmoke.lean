import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)

noncomputable def finite_wilson_free_positive_coercive_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W :=
  D.toCoerciveTransferOrbitData

theorem finite_wilson_free_positive_total_coercive_compile_smoke
    (n : ℕ) (x : D.StateSpace) :
    exactGapValueReal * ‖x‖ ^ 2 ≤ inner ℝ (D.hamiltonian n x) x :=
  finite_wilson_free_positive_total_hamiltonian_coercive D n x

theorem finite_wilson_free_positive_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin D.StateDimension) :
    exactGapValueReal ≤
      (finite_wilson_free_positive_total_hamiltonian_symmetric D n).eigenvalues
        D.stateFinrank i :=
  finite_wilson_free_positive_hamiltonian_eigenvalues_ge_exactGap D n i

theorem finite_wilson_free_positive_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_free_positive_interaction_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
