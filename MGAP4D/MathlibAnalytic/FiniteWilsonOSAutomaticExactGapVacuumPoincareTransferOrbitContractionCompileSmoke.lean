import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (G : FiniteWilsonVacuumPoincareHamiltonianGapData)

noncomputable def finite_wilson_vacuum_poincare_gap_data_compile_smoke :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  G.toDerivedInvarianceGapData

theorem finite_wilson_vacuum_poincare_coercive_compile_smoke
    (n : ℕ) (x : G.StateSpace)
    (hx : x ∈ finiteVacuumOrthogonal G.vacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤ inner ℝ (G.hamiltonian n x) x :=
  finite_wilson_vacuum_poincare_implies_orthogonal_coercivity G n x hx

theorem finite_wilson_vacuum_poincare_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        G.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          G.excitedFinrank i :=
  finite_wilson_vacuum_poincare_restricted_eigenvalues_ge_exactGap G n i

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W)

noncomputable def finite_wilson_vacuum_poincare_transfer_data_compile_smoke :
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W :=
  D.toDerivedInvarianceData

theorem finite_wilson_vacuum_poincare_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_poincare_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
