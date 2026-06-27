import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalDerivedInvarianceGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The component of a state centered by its vacuum expectation. -/
def finiteVacuumCentered
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (vacuum x : E) : E :=
  x - inner ℝ vacuum x • vacuum

/-- For a normalized real Hilbert-space vacuum, vacuum centering subtracts
exactly the squared vacuum coefficient from the squared norm. -/
theorem finite_vacuum_centered_norm_sq
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (vacuum : E) (hvacuum : ‖vacuum‖ = 1) (x : E) :
    ‖finiteVacuumCentered vacuum x‖ ^ 2 =
      ‖x‖ ^ 2 - (inner ℝ vacuum x) ^ 2 := by
  have hvacuumInner : inner ℝ vacuum vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, hvacuum]
    norm_num
  have hcomm : inner ℝ x vacuum = inner ℝ vacuum x :=
    (real_inner_comm x vacuum).symm
  calc
    ‖finiteVacuumCentered vacuum x‖ ^ 2 =
        inner ℝ (finiteVacuumCentered vacuum x)
          (finiteVacuumCentered vacuum x) := by
      simpa using
        (real_inner_self_eq_norm_sq
          (finiteVacuumCentered vacuum x)).symm
    _ = ‖x‖ ^ 2 - (inner ℝ vacuum x) ^ 2 := by
      simp [finiteVacuumCentered, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
        hcomm, hvacuumInner]
      ring

/-- Finite Wilson Hamiltonian data in which the excitation-sector gap is
reduced to a Dirichlet-form representation and a uniform vacuum-centered
Poincare inequality. -/
structure FiniteWilsonVacuumPoincareHamiltonianGapData where
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
  dirichletForm : ℕ → StateSpace → ℝ
  hamiltonianQuadraticForm_eq_dirichletForm :
    ∀ (n : ℕ) (x : StateSpace),
      inner ℝ (hamiltonian n x) x = dirichletForm n x
  vacuumPoincareInequality :
    ∀ (n : ℕ) (x : StateSpace),
      exactGapValueReal * ‖finiteVacuumCentered vacuum x‖ ^ 2 ≤
        dirichletForm n x
  ExcitedDimension : ℕ
  excitedFinrank :
    Module.finrank ℝ (finiteVacuumOrthogonal vacuum) = ExcitedDimension

attribute [instance]
  FiniteWilsonVacuumPoincareHamiltonianGapData.stateNormedAddCommGroup
  FiniteWilsonVacuumPoincareHamiltonianGapData.stateInnerProductSpace
  FiniteWilsonVacuumPoincareHamiltonianGapData.stateFiniteDimensional

/-- A vacuum-centered Poincare inequality gives Hamiltonian coercivity on the
physical excitation sector. -/
theorem finite_wilson_vacuum_poincare_implies_orthogonal_coercivity
    (G : FiniteWilsonVacuumPoincareHamiltonianGapData)
    (n : ℕ) (x : G.StateSpace)
    (hx : x ∈ finiteVacuumOrthogonal G.vacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (G.hamiltonian n x) x := by
  have hOrth : inner ℝ G.vacuum x = 0 :=
    (finite_wilson_mem_vacuumOrthogonal_iff G.vacuum x).mp hx
  calc
    exactGapValueReal * ‖x‖ ^ 2 =
        exactGapValueReal * ‖finiteVacuumCentered G.vacuum x‖ ^ 2 := by
      simp [finiteVacuumCentered, hOrth]
    _ ≤ G.dirichletForm n x :=
      G.vacuumPoincareInequality n x
    _ = inner ℝ (G.hamiltonian n x) x :=
      (G.hamiltonianQuadraticForm_eq_dirichletForm n x).symm

/-- Convert the Poincare package to the reduced vacuum-orthogonal Hamiltonian
package.  Sector invariance and spectral control are then theorem-generated. -/
noncomputable def
    FiniteWilsonVacuumPoincareHamiltonianGapData.toDerivedInvarianceGapData
    (G : FiniteWilsonVacuumPoincareHamiltonianGapData) :
    FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData :=
  { StateSpace := G.StateSpace
    stateNormedAddCommGroup := G.stateNormedAddCommGroup
    stateInnerProductSpace := G.stateInnerProductSpace
    stateFiniteDimensional := G.stateFiniteDimensional
    vacuum := G.vacuum
    vacuum_norm := G.vacuum_norm
    hamiltonian := G.hamiltonian
    hamiltonianSymmetric := G.hamiltonianSymmetric
    vacuumEnergyZero := G.vacuumEnergyZero
    hamiltonianQuadraticFormLowerBoundOnVacuumOrthogonal :=
      finite_wilson_vacuum_poincare_implies_orthogonal_coercivity G
    ExcitedDimension := G.ExcitedDimension
    excitedFinrank := G.excitedFinrank }

/-- The Poincare inequality generates the exact lower bound for every
excitation-sector Hamiltonian eigenvalue. -/
theorem finite_wilson_vacuum_poincare_restricted_eigenvalues_ge_exactGap
    (G : FiniteWilsonVacuumPoincareHamiltonianGapData)
    (n : ℕ) (i : Fin G.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        G.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          G.excitedFinrank i :=
  finite_wilson_derived_invariance_restricted_eigenvalues_ge_exactGap
    G.toDerivedInvarianceGapData n i

end

end MathlibAnalytic
end MGAP4D
