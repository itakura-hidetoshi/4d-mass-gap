import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite Wilson Hamiltonian data in which the global vacuum Poincare
inequality is reduced to local conditional variances, local Dirichlet energies,
and a tensorization estimate.  The update sites may later be instantiated by
links, blocks, plaquettes, or gauge-fixed local coordinates. -/
structure FiniteWilsonVacuumLocalPoincareTensorizationGapData where
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
  UpdateSite : Type
  [updateSiteFintype : Fintype UpdateSite]
  localVariance : ℕ → UpdateSite → StateSpace → ℝ
  localDirichletForm : ℕ → UpdateSite → StateSpace → ℝ
  varianceTensorization :
    ∀ (n : ℕ) (x : StateSpace),
      ‖finiteVacuumCentered vacuum x‖ ^ 2 ≤
        ∑ s : UpdateSite, localVariance n s x
  localPoincareInequality :
    ∀ (n : ℕ) (s : UpdateSite) (x : StateSpace),
      exactGapValueReal * localVariance n s x ≤
        localDirichletForm n s x
  hamiltonianQuadraticForm_eq_sum_localDirichlet :
    ∀ (n : ℕ) (x : StateSpace),
      inner ℝ (hamiltonian n x) x =
        ∑ s : UpdateSite, localDirichletForm n s x
  ExcitedDimension : ℕ
  excitedFinrank :
    Module.finrank ℝ (finiteVacuumOrthogonal vacuum) = ExcitedDimension

attribute [instance]
  FiniteWilsonVacuumLocalPoincareTensorizationGapData.stateNormedAddCommGroup
  FiniteWilsonVacuumLocalPoincareTensorizationGapData.stateInnerProductSpace
  FiniteWilsonVacuumLocalPoincareTensorizationGapData.stateFiniteDimensional
  FiniteWilsonVacuumLocalPoincareTensorizationGapData.updateSiteFintype

/-- Local Poincare inequalities plus variance tensorization generate the global
vacuum-centered Poincare inequality. -/
theorem finite_wilson_local_poincare_tensorization_implies_global_poincare
    (G : FiniteWilsonVacuumLocalPoincareTensorizationGapData)
    (n : ℕ) (x : G.StateSpace) :
    exactGapValueReal * ‖finiteVacuumCentered G.vacuum x‖ ^ 2 ≤
      ∑ s : G.UpdateSite, G.localDirichletForm n s x := by
  calc
    exactGapValueReal * ‖finiteVacuumCentered G.vacuum x‖ ^ 2 ≤
        exactGapValueReal *
          (∑ s : G.UpdateSite, G.localVariance n s x) :=
      mul_le_mul_of_nonneg_left
        (G.varianceTensorization n x)
        (le_of_lt exactGapValueReal_pos)
    _ = ∑ s : G.UpdateSite,
        exactGapValueReal * G.localVariance n s x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ s : G.UpdateSite, G.localDirichletForm n s x := by
      exact Finset.sum_le_sum fun s _hs =>
        G.localPoincareInequality n s x

/-- Convert the local-update package to the global Wilson Poincare package.
After this conversion all vacuum-sector, spectral, transfer, clustering, and
continuum OS consequences are theorem-generated. -/
noncomputable def
    FiniteWilsonVacuumLocalPoincareTensorizationGapData.toVacuumPoincareGapData
    (G : FiniteWilsonVacuumLocalPoincareTensorizationGapData) :
    FiniteWilsonVacuumPoincareHamiltonianGapData :=
  { StateSpace := G.StateSpace
    stateNormedAddCommGroup := G.stateNormedAddCommGroup
    stateInnerProductSpace := G.stateInnerProductSpace
    stateFiniteDimensional := G.stateFiniteDimensional
    vacuum := G.vacuum
    vacuum_norm := G.vacuum_norm
    hamiltonian := G.hamiltonian
    hamiltonianSymmetric := G.hamiltonianSymmetric
    vacuumEnergyZero := G.vacuumEnergyZero
    dirichletForm := fun n x =>
      ∑ s : G.UpdateSite, G.localDirichletForm n s x
    hamiltonianQuadraticForm_eq_dirichletForm :=
      G.hamiltonianQuadraticForm_eq_sum_localDirichlet
    vacuumPoincareInequality :=
      finite_wilson_local_poincare_tensorization_implies_global_poincare G
    ExcitedDimension := G.ExcitedDimension
    excitedFinrank := G.excitedFinrank }

/-- The local-update assumptions generate every excitation-sector eigenvalue
lower bound. -/
theorem finite_wilson_local_poincare_restricted_eigenvalues_ge_exactGap
    (G : FiniteWilsonVacuumLocalPoincareTensorizationGapData)
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        G.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          G.excitedFinrank i :=
  finite_wilson_vacuum_poincare_restricted_eigenvalues_ge_exactGap
    G.toVacuumPoincareGapData n i

end

end MathlibAnalytic
end MGAP4D
