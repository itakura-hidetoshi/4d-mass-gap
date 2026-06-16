import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (G : FiniteWilsonVacuumOrthogonalHamiltonianGapData)

noncomputable def finite_wilson_vacuum_orthogonal_restricted_hamiltonian_compile_smoke
    (n : ℕ) : G.ExcitedStateSpace →ₗ[ℝ] G.ExcitedStateSpace :=
  G.restrictedHamiltonian n

theorem finite_wilson_vacuum_orthogonal_symmetric_compile_smoke
    (n : ℕ) :
    (G.restrictedHamiltonian n).IsSymmetric :=
  finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric G n

theorem finite_wilson_vacuum_orthogonal_coercive_compile_smoke
    (n : ℕ) (x : G.ExcitedStateSpace) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (G.restrictedHamiltonian n x) x :=
  finite_wilson_vacuum_orthogonal_restricted_hamiltonian_coercive G n x

theorem finite_wilson_vacuum_orthogonal_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric G n).eigenvalues
        G.excitedFinrank i :=
  finite_wilson_vacuum_orthogonal_restricted_eigenvalues_ge_exactGap G n i

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)

noncomputable def finite_wilson_vacuum_orthogonal_to_coercive_compile_smoke :
    FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W :=
  D.toCoerciveTransferOrbitData

theorem finite_wilson_vacuum_orthogonal_continuum_bound_compile_smoke
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_orthogonal_coercive_continuum_bound D O r

end

end MathlibAnalytic
end MGAP4D
