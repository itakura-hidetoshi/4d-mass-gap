import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W)

noncomputable def finite_wilson_coercive_transfer_orbit_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W :=
  D.toConstructedTransferOrbitData

theorem finite_wilson_coercive_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin D.StateDimension) :
    exactGapValueReal ≤
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i :=
  finite_wilson_coercive_hamiltonian_eigenvalues_ge_exactGap D n i

theorem finite_wilson_coercive_operator_bound_compile_smoke
    (n : ℕ) :
    ‖D.toConstructedTransferOrbitData.transferOperator n‖ ≤
      exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_coercive_hamiltonian D n

theorem finite_wilson_coercive_finite_bound_compile_smoke
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_coercive_hamiltonian D n O r

theorem finite_wilson_coercive_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_coercive_hamiltonian_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
