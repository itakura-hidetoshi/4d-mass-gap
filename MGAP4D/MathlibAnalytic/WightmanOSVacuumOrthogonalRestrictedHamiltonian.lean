import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalSpectrumGap
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The domain `D(H) ∩ Ω⊥`, represented as a submodule of the physical
vacuum-orthogonal Hilbert carrier. -/
def ExplicitWightmanOSReconstructedModel.vacuumOrthogonalHamiltonianDomain
    (M : ExplicitWightmanOSReconstructedModel) :
    Submodule ℝ M.VacuumOrthogonalHilbert where
  carrier := {ψ | (ψ : M.H) ∈ M.hamiltonian.domain}
  zero_mem' := by
    change (0 : M.H) ∈ M.hamiltonian.domain
    exact M.hamiltonian.domain.zero_mem
  add_mem' := by
    intro x y hx hy
    change (x : M.H) ∈ M.hamiltonian.domain at hx
    change (y : M.H) ∈ M.hamiltonian.domain at hy
    change (x : M.H) + (y : M.H) ∈ M.hamiltonian.domain
    exact M.hamiltonian.domain.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change (x : M.H) ∈ M.hamiltonian.domain at hx
    change c • (x : M.H) ∈ M.hamiltonian.domain
    exact M.hamiltonian.domain.smul_mem c hx

/-- A domain point of the restricted Hamiltonian, viewed as a domain point of the
ambient Hamiltonian. -/
def ExplicitWightmanOSReconstructedModel.vacuumOrthogonalAmbientDomainPoint
    (M : ExplicitWightmanOSReconstructedModel)
    (x : M.vacuumOrthogonalHamiltonianDomain) :
    M.hamiltonian.domain :=
  ⟨((x : M.VacuumOrthogonalHilbert) : M.H), x.property⟩

/-- The standard reducing-subspace input needed to define `H|Ω⊥`: the ambient
Hamiltonian maps every vector in `D(H) ∩ Ω⊥` back into `Ω⊥`. -/
structure ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant
    (M : ExplicitWightmanOSReconstructedModel) where
  map_mem :
    ∀ x : M.hamiltonian.domain,
      (x : M.H) ∈ M.vacuumOrthogonal →
        M.hamiltonian x ∈ M.vacuumOrthogonal

/-- The ambient Hamiltonian action bundled as a linear map from
`D(H) ∩ Ω⊥` into `Ω⊥`. -/
def ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant.restrictedLinearMap
    {M : ExplicitWightmanOSReconstructedModel}
    (I : ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M) :
    M.vacuumOrthogonalHamiltonianDomain →ₗ[ℝ]
      M.VacuumOrthogonalHilbert where
  toFun := fun x =>
    ⟨M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x),
      I.map_mem (M.vacuumOrthogonalAmbientDomainPoint x)
        (x : M.VacuumOrthogonalHilbert).property⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonalAmbientDomainPoint]
      using M.hamiltonian.toFun.map_add
        (M.vacuumOrthogonalAmbientDomainPoint x)
        (M.vacuumOrthogonalAmbientDomainPoint y)
  map_smul' := by
    intro c x
    apply Subtype.ext
    simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonalAmbientDomainPoint]
      using M.hamiltonian.toFun.map_smul c
        (M.vacuumOrthogonalAmbientDomainPoint x)

/-- The actual partially-defined Hamiltonian restricted to the physical
vacuum-orthogonal Hilbert sector. -/
def ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant.restrictedHamiltonian
    {M : ExplicitWightmanOSReconstructedModel}
    (I : ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M) :
    M.VacuumOrthogonalHilbert →ₗ.[ℝ]
      M.VacuumOrthogonalHilbert :=
  { domain := M.vacuumOrthogonalHamiltonianDomain
    toFun := I.restrictedLinearMap }

/-- The restricted operator has exactly the intersection domain
`D(H) ∩ Ω⊥`. -/
theorem vacuum_orthogonal_restrictedHamiltonian_domain
    {M : ExplicitWightmanOSReconstructedModel}
    (I : ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M) :
    I.restrictedHamiltonian.domain =
      M.vacuumOrthogonalHamiltonianDomain := by
  rfl

/-- After inclusion into the ambient Hilbert space, the restricted Hamiltonian
acts exactly as the original Hamiltonian. -/
theorem vacuum_orthogonal_restrictedHamiltonian_apply
    {M : ExplicitWightmanOSReconstructedModel}
    (I : ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M)
    (x : I.restrictedHamiltonian.domain) :
    ((I.restrictedHamiltonian x : M.VacuumOrthogonalHilbert) : M.H) =
      M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x) := by
  rfl

/-- A theorem-level bridge joining the actual restricted operator to the
previously isolated non-vacuum spectral set.  Self-adjointness of the restricted
operator and equality with its operator-theoretic spectrum remain explicit
inputs rather than being hidden in the set-theoretic bridge. -/
structure ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge
    (M : ExplicitWightmanOSReconstructedModel) extends
      ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M where
  invariant : ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M
  restrictedHamiltonianSelfAdjoint :
    IsSelfAdjoint invariant.restrictedHamiltonian

/-- The restricted-Hamiltonian bridge exposes an actual Mathlib `LinearPMap` on
`Ω⊥`, not merely a set named as a restricted spectrum. -/
def ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge.operator
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge M) :
    M.VacuumOrthogonalHilbert →ₗ.[ℝ]
      M.VacuumOrthogonalHilbert :=
  B.invariant.restrictedHamiltonian

/-- The actual restricted operator is self-adjoint by the bridge input. -/
theorem vacuum_orthogonal_restrictedHamiltonian_isSelfAdjoint
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge M) :
    IsSelfAdjoint B.operator :=
  B.restrictedHamiltonianSelfAdjoint

end

end MathlibAnalytic
end MGAP4D
