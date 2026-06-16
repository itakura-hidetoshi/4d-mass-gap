import MGAP4D.MathlibAnalytic.FiniteWilsonSingleLinkHeatBathHamiltonianBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (D : FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData W)

noncomputable def finite_wilson_single_link_heat_bath_gap_data_compile_smoke :
    FiniteWilsonVacuumPoincareHamiltonianGapData :=
  D.toVacuumPoincareGapData

theorem finite_wilson_single_link_heat_bath_vacuum_poincare_compile_smoke
    (n : ℕ) (x : D.StateSpace) :
    exactGapValueReal * ‖finiteVacuumCentered D.vacuum x‖ ^ 2 ≤
      inner ℝ (D.hamiltonian n x) x :=
  finite_wilson_single_link_heat_bath_implies_vacuum_poincare D n x

theorem finite_wilson_single_link_heat_bath_eigenvalue_compile_smoke
    (n : ℕ) (i : Fin D.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        D.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          D.excitedFinrank i :=
  finite_wilson_single_link_heat_bath_restricted_eigenvalues_ge_exactGap D n i

end

end MathlibAnalytic
end MGAP4D
