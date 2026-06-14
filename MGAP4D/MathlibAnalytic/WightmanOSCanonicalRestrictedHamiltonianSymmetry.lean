import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical restriction `H|Ω⊥` is a formal adjoint of itself.  This is the
operator-theoretic symmetry inherited from ambient self-adjointness; the
remaining promotion from symmetry to self-adjointness is the maximal-domain
obligation. -/
theorem canonical_vacuum_orthogonal_hamiltonian_isFormalSelfAdjoint
    (M : ExplicitWightmanOSReconstructedModel) :
    M.canonicalVacuumOrthogonalHamiltonian.IsFormalAdjoint
      M.canonicalVacuumOrthogonalHamiltonian := by
  intro x y
  change
    inner ℝ
        (M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x))
        ((y : M.VacuumOrthogonalHilbert) : M.H) =
      inner ℝ
        ((x : M.VacuumOrthogonalHilbert) : M.H)
        (M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint y))
  exact
    explicit_wightman_os_hamiltonian_isFormalSelfAdjoint M
      (M.vacuumOrthogonalAmbientDomainPoint x)
      (M.vacuumOrthogonalAmbientDomainPoint y)

/-- Symmetry of the actual restriction no longer needs to be included as an
independent bridge field. -/
theorem canonical_vacuum_orthogonal_hamiltonian_symmetric_matrix_coefficient
    (M : ExplicitWightmanOSReconstructedModel)
    (x y : M.canonicalVacuumOrthogonalHamiltonian.domain) :
    inner ℝ
        (M.canonicalVacuumOrthogonalHamiltonian x)
        (y : M.VacuumOrthogonalHilbert) =
      inner ℝ
        (x : M.VacuumOrthogonalHilbert)
        (M.canonicalVacuumOrthogonalHamiltonian y) := by
  exact canonical_vacuum_orthogonal_hamiltonian_isFormalSelfAdjoint M x y

/-- The remaining operator-level promotion obligation is explicitly isolated as
equality between the adjoint and the canonical restriction. -/
def CanonicalVacuumOrthogonalHamiltonianMaximality
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  M.canonicalVacuumOrthogonalHamiltonian.adjoint =
    M.canonicalVacuumOrthogonalHamiltonian

/-- The maximality equality is exactly self-adjointness in Mathlib's `LinearPMap`
model. -/
theorem canonical_vacuum_orthogonal_hamiltonian_maximality_iff_selfAdjoint
    (M : ExplicitWightmanOSReconstructedModel) :
    CanonicalVacuumOrthogonalHamiltonianMaximality M ↔
      IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian := by
  exact LinearPMap.isSelfAdjoint_def.symm

/-- A maximal canonical restriction is densely defined and closed. -/
theorem canonical_vacuum_orthogonal_hamiltonian_maximality_operator_package
    (M : ExplicitWightmanOSReconstructedModel)
    (hMaximal : CanonicalVacuumOrthogonalHamiltonianMaximality M) :
    Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
      Set M.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian := by
  have hSelfAdjoint :
      IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian :=
    (canonical_vacuum_orthogonal_hamiltonian_maximality_iff_selfAdjoint M).mp
      hMaximal
  exact ⟨hSelfAdjoint.dense_domain, hSelfAdjoint.isClosed⟩

end

end MathlibAnalytic
end MGAP4D
