import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (G : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData)

noncomputable def finite_wilson_derived_invariance_gap_data_compile_smoke :
    FiniteWilsonVacuumOrthogonalHamiltonianGapData :=
  G.toVacuumOrthogonalGapData

theorem finite_wilson_derived_invariance_compile_smoke
    (n : ℕ) (x : G.StateSpace)
    (hx : x ∈ finiteVacuumOrthogonal G.vacuum) :
    G.hamiltonian n x ∈ finiteVacuumOrthogonal G.vacuum :=
  finite_wilson_derived_hamiltonian_preserves_vacuumOrthogonal G n x hx

theorem finite_wilson_derived_invariance_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        G.toVacuumOrthogonalGapData n).eigenvalues G.excitedFinrank i :=
  finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap G n i

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W)

noncomputable def finite_wilson_derived_invariance_transfer_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W :=
  D.toVacuumOrthogonalData

theorem finite_wilson_derived_invariance_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_orthogonal_derived_invariance_continuum_bound
    D O r

end

end MathlibAnalytic
end MGAP4D
