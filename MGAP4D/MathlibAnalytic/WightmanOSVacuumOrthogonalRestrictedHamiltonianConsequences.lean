import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianSymmetry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical restricted Hamiltonian has dense intersection domain
`D(H) ∩ Ω⊥` in the physical non-vacuum Hilbert sector. -/
theorem vacuum_orthogonal_restrictedHamiltonian_dense_domain
    (M : ExplicitWightmanOSReconstructedModel) :
    Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
      Set M.VacuumOrthogonalHilbert)) := by
  exact
    explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_dense_domain M

/-- The canonical restricted Hamiltonian is a closed partially-defined operator. -/
theorem vacuum_orthogonal_restrictedHamiltonian_isClosed
    (M : ExplicitWightmanOSReconstructedModel) :
    LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian := by
  exact
    explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isClosed M

/-- The canonical operator-level physical sector exposes all three basic analytic
facts: actual restriction to `D(H) ∩ Ω⊥`, dense domain, and closed graph. -/
theorem vacuum_orthogonal_restrictedHamiltonian_operator_package
    (M : ExplicitWightmanOSReconstructedModel) :
    M.canonicalVacuumOrthogonalHamiltonian.domain =
        M.vacuumOrthogonalHamiltonianDomain ∧
      Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
        Set M.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian := by
  exact ⟨canonical_vacuum_orthogonal_hamiltonian_domain M,
    vacuum_orthogonal_restrictedHamiltonian_dense_domain M,
    vacuum_orthogonal_restrictedHamiltonian_isClosed M⟩

end

end MathlibAnalytic
end MGAP4D
