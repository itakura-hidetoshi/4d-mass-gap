import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Self-adjointness of the actual restricted Hamiltonian forces its intersection
domain `D(H) ∩ Ω⊥` to be dense in the physical non-vacuum Hilbert sector. -/
theorem vacuum_orthogonal_restrictedHamiltonian_dense_domain
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge M) :
    Dense ((B.operator.domain : Set M.VacuumOrthogonalHilbert)) := by
  exact (vacuum_orthogonal_restrictedHamiltonian_isSelfAdjoint B).dense_domain

/-- The actual restricted Hamiltonian is a closed partially-defined operator. -/
theorem vacuum_orthogonal_restrictedHamiltonian_isClosed
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge M) :
    LinearPMap.IsClosed B.operator := by
  exact (vacuum_orthogonal_restrictedHamiltonian_isSelfAdjoint B).isClosed

/-- The operator-level physical sector now exposes all three basic analytic facts:
actual restriction to `D(H) ∩ Ω⊥`, dense domain, and closed graph. -/
theorem vacuum_orthogonal_restrictedHamiltonian_operator_package
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge M) :
    B.operator.domain = M.vacuumOrthogonalHamiltonianDomain ∧
      Dense ((B.operator.domain : Set M.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed B.operator := by
  exact ⟨rfl,
    vacuum_orthogonal_restrictedHamiltonian_dense_domain B,
    vacuum_orthogonal_restrictedHamiltonian_isClosed B⟩

end

end MathlibAnalytic
end MGAP4D
