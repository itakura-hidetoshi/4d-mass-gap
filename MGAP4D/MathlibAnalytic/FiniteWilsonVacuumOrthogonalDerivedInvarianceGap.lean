import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalInvariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-volume Hamiltonian gap data without an independent invariance field.
The invariance of the vacuum-orthogonal sector is generated from symmetry and
zero vacuum energy. -/
structure FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData where
  StateSpace : Type
  [stateNormedAddCommGroup : NormedAddCommGroup StateSpace]
  [stateInnerProductSpace : InnerProductSpace ℝ StateSpace]
  [stateFiniteDimensional : FiniteDimensional ℝ StateSpace]
  vacuum : StateSpace
  vacuum_norm : ‖vacuum‖ = 1
  hamiltonian : ℕ → StateSpace →ₗ[ℝ] StateSpace
  hamiltonianSymmetric :
    ∀ n : ℕ, (hamiltonian n).IsSymmetric
  vacuumEnergyZero :
    ∀ n : ℕ, hamiltonian n vacuum = 0
  hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal :
    ∀ (n : ℕ) (x : StateSpace),
      x ∈ finiteVacuumOrthogonal vacuum →
        exactGapValueReal * ‖x‖ ^ 2 ≤
          inner ℝ (hamiltonian n x) x
  ExcitedDimension : ℕ
  excitedFinrank :
    Module.finrank ℝ (finiteVacuumOrthogonal vacuum) = ExcitedDimension

attribute [instance]
  FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData.stateNormedAddCommGroup
  FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData.stateInnerProductSpace
  FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData.stateFiniteDimensional

/-- The vacuum-orthogonal invariance theorem specialized to the finite Wilson
Hamiltonian family. -/
theorem finite_wilson_derived_hamiltonian_preserves_vacuumOrthogonal
    (G : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData)
    (n : ℕ) (x : G.StateSpace)
    (hx : x ∈ finiteVacuumOrthogonal G.vacuum) :
    G.hamiltonian n x ∈ finiteVacuumOrthogonal G.vacuum :=
  symmetric_zero_vacuum_preserves_vacuumOrthogonal
    G.vacuum (G.hamiltonian n)
    (G.hamiltonianSymmetric n) (G.vacuumEnergyZero n) hx

/-- Convert to the established vacuum-orthogonal package only after invariance
has been theorem-generated. -/
noncomputable def
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData.toVacuumOrthogonalGapData
    (G : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData) :
    FiniteWilsonVacuumOrthogonalHamiltonianGapData :=
  { StateSpace := G.StateSpace
    stateNormedAddCommGroup := G.stateNormedAddCommGroup
    stateInnerProductSpace := G.stateInnerProductSpace
    stateFiniteDimensional := G.stateFiniteDimensional
    vacuum := G.vacuum
    vacuum_norm := G.vacuum_norm
    hamiltonian := G.hamiltonian
    hamiltonianSymmetric := G.hamiltonianSymmetric
    vacuumEnergyZero := G.vacuumEnergyZero
    hamiltonianPreservesVacuumOrthogonal :=
      finite_wilson_derived_hamiltonian_preserves_vacuumOrthogonal G
    hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal :=
      G.hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal
    ExcitedDimension := G.ExcitedDimension
    excitedFinrank := G.excitedFinrank }

/-- Excitation-sector carrier generated from the reduced data. -/
abbrev FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData.ExcitedStateSpace
    (G : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData) : Type :=
  G.toVacuumOrthogonalGapData.ExcitedStateSpace

/-- Hamiltonian restricted to the generated invariant excitation sector. -/
noncomputable def
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData.restrictedHamiltonian
    (G : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData)
    (n : ℕ) : G.ExcitedStateSpace →ₗ[ℝ] G.ExcitedStateSpace :=
  G.toVacuumOrthogonalGapData.restrictedHamiltonian n

/-- Every generated excitation-sector eigenvalue lies above the exact gap. -/
theorem finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap
    (G : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData)
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        G.toVacuumOrthogonalGapData n).eigenvalues G.excitedFinrank i :=
  finite_wilson_vacuum_orthogonal_restricted_eigenvalues_ge_exactGap
    G.toVacuumOrthogonalGapData n i

end

end MathlibAnalytic
end MGAP4D
