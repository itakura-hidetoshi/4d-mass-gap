import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (G : FiniteWilsonVacuumLocalPoincareTensorizationGapData)

noncomputable def finite_wilson_local_poincare_gap_data_compile_smoke :
    FiniteWilsonVacuumPoincareHamiltonianGapData :=
  G.toVacuumPoincareGapData

theorem finite_wilson_local_poincare_global_compile_smoke
    (n : ℕ) (x : G.StateSpace) :
    exactGapValueReal * ‖finiteVacuumCentered G.vacuum x‖ ^ 2 ≤
      ∑ s : G.UpdateSite, G.localDirichletForm n s x :=
  finite_wilson_local_poincare_tensorization_implies_global_poincare G n x

theorem finite_wilson_local_poincare_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        G.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          G.excitedFinrank i :=
  finite_wilson_local_poincare_restricted_eigenvalues_ge_exactGap G n i

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContractionData W)

noncomputable def finite_wilson_local_poincare_transfer_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W :=
  D.toVacuumPoincareData

theorem finite_wilson_local_poincare_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_local_poincare_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
