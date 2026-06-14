import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalRestrictedHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A self-adjoint reconstructed Hamiltonian is a formal adjoint of itself on its
domain. -/
theorem explicit_wightman_os_hamiltonian_isFormalSelfAdjoint
    (M : ExplicitWightmanOSReconstructedModel) :
    M.hamiltonian.IsFormalAdjoint M.hamiltonian := by
  have hDense : Dense ((M.hamiltonian.domain : Set M.H)) :=
    M.hamiltonianSelfAdjoint.dense_domain
  have hFormal :
      M.hamiltonian.adjoint.IsFormalAdjoint M.hamiltonian :=
    LinearPMap.adjoint_isFormalAdjoint hDense
  have hAdjoint : M.hamiltonian.adjoint = M.hamiltonian :=
    LinearPMap.isSelfAdjoint_def.mp M.hamiltonianSelfAdjoint
  rw [hAdjoint] at hFormal
  exact hFormal

/-- Self-adjointness together with the zero-energy vacuum implies that the
Hamiltonian preserves the physical vacuum-orthogonal sector. -/
def explicitWightmanOSVacuumOrthogonalHamiltonianInvariantOfSelfAdjoint
    (M : ExplicitWightmanOSReconstructedModel) :
    ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M where
  map_mem := by
    intro x hx
    apply (explicit_wightman_os_mem_vacuumOrthogonal_iff
      M (M.hamiltonian x)).2
    have hFormal := explicit_wightman_os_hamiltonian_isFormalSelfAdjoint M
    have hVacuumSymmetry :=
      hFormal
        ⟨M.vacuum, M.vacuum_mem_hamiltonianDomain⟩
        x
    calc
      inner ℝ M.vacuum (M.hamiltonian x) =
          inner ℝ
            (M.hamiltonian
              ⟨M.vacuum, M.vacuum_mem_hamiltonianDomain⟩)
            (x : M.H) := hVacuumSymmetry.symm
      _ = inner ℝ 0 (x : M.H) := by
        rw [M.vacuumEnergyZero]
      _ = 0 := by simp

/-- The canonical actual Hamiltonian restriction obtained directly from ambient
self-adjointness and the zero-energy vacuum. -/
def ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalHamiltonian
    (M : ExplicitWightmanOSReconstructedModel) :
    M.VacuumOrthogonalHilbert →ₗ.[ℝ]
      M.VacuumOrthogonalHilbert :=
  (explicitWightmanOSVacuumOrthogonalHamiltonianInvariantOfSelfAdjoint M).restrictedHamiltonian

/-- The canonical restriction has exactly the intersection domain
`D(H) ∩ Ω⊥`. -/
theorem canonical_vacuum_orthogonal_hamiltonian_domain
    (M : ExplicitWightmanOSReconstructedModel) :
    M.canonicalVacuumOrthogonalHamiltonian.domain =
      M.vacuumOrthogonalHamiltonianDomain := by
  rfl

/-- The canonical restriction agrees pointwise with the ambient Hamiltonian after
inclusion into the physical Hilbert space. -/
theorem canonical_vacuum_orthogonal_hamiltonian_apply
    (M : ExplicitWightmanOSReconstructedModel)
    (x : M.canonicalVacuumOrthogonalHamiltonian.domain) :
    ((M.canonicalVacuumOrthogonalHamiltonian x :
        M.VacuumOrthogonalHilbert) : M.H) =
      M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x) := by
  rfl

/-- Reduced bridge: Hamiltonian invariance is now derived.  Only
self-adjointness of the canonical restriction and the spectral identification
remain explicit operator-level inputs. -/
structure ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
    (M : ExplicitWightmanOSReconstructedModel) extends
      ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M where
  canonicalRestrictedSelfAdjoint :
    IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian

/-- The canonical restricted Hamiltonian has dense intersection domain. -/
theorem canonical_vacuum_orthogonal_hamiltonian_dense_domain
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M) :
    Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
      Set M.VacuumOrthogonalHilbert)) := by
  exact B.canonicalRestrictedSelfAdjoint.dense_domain

/-- The canonical restricted Hamiltonian is closed. -/
theorem canonical_vacuum_orthogonal_hamiltonian_isClosed
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M) :
    LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian := by
  exact B.canonicalRestrictedSelfAdjoint.isClosed

end

end MathlibAnalytic
end MGAP4D
