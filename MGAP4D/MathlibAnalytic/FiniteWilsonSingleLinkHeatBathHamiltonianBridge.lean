import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathVariance
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticApproximationFamily

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A realization bridge from finite-dimensional Hamiltonian states to real
observables on concrete finite Wilson configurations.  The centered Hilbert
norm is identified with the Wilson Gibbs variance, while the Hamiltonian
quadratic form is identified with the exact single-link heat-bath Dirichlet
form. -/
structure FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
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
  scale : ℕ → W.index
  observableRealization :
    (n : ℕ) →
      StateSpace →ₗ[ℝ] ((W.system (scale n)).Configuration → ℝ)
  centeredNormSq_eq_gibbsVariance :
    ∀ (n : ℕ) (x : StateSpace),
      ‖finiteVacuumCentered vacuum x‖ ^ 2 =
        (W.system (scale n)).gibbsVarianceReal
          (observableRealization n x)
  hamiltonianQuadraticForm_eq_heatBathDirichlet :
    ∀ (n : ℕ) (x : StateSpace),
      inner ℝ (hamiltonian n x) x =
        (W.system (scale n)).singleLinkHeatBathDirichletForm
          (observableRealization n x)
  exactGapSingleLinkHeatBathPoincare :
    ∀ n : ℕ,
      (W.system (scale n)).ExactGapSingleLinkHeatBathPoincare
  ExcitedDimension : ℕ
  excitedFinrank :
    Module.finrank ℝ (finiteVacuumOrthogonal vacuum) = ExcitedDimension

attribute [instance]
  FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData.stateNormedAddCommGroup
  FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData.stateInnerProductSpace
  FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData.stateFiniteDimensional

/-- A concrete single-link heat-bath Poincare estimate generates the abstract
vacuum-centered Hamiltonian Poincare package used by the full spectral and
continuum construction. -/
noncomputable def
    FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData.toVacuumPoincareGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData W) :
    FiniteWilsonVacuumPoincareHamiltonianGapData :=
  { StateSpace := D.StateSpace
    stateNormedAddCommGroup := D.stateNormedAddCommGroup
    stateInnerProductSpace := D.stateInnerProductSpace
    stateFiniteDimensional := D.stateFiniteDimensional
    vacuum := D.vacuum
    vacuum_norm := D.vacuum_norm
    hamiltonian := D.hamiltonian
    hamiltonianSymmetric := D.hamiltonianSymmetric
    vacuumEnergyZero := D.vacuumEnergyZero
    dirichletForm := fun n x =>
      (W.system (D.scale n)).singleLinkHeatBathDirichletForm
        (D.observableRealization n x)
    hamiltonianQuadraticForm_eq_dirichletForm :=
      D.hamiltonianQuadraticForm_eq_heatBathDirichlet
    vacuumPoincareInequality := by
      intro n x
      rw [D.centeredNormSq_eq_gibbsVariance n x]
      exact D.exactGapSingleLinkHeatBathPoincare n
        (D.observableRealization n x)
    ExcitedDimension := D.ExcitedDimension
    excitedFinrank := D.excitedFinrank }

/-- The concrete heat-bath bridge generates the global vacuum-centered
Poincare inequality. -/
theorem finite_wilson_single_link_heat_bath_implies_vacuum_poincare
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData W)
    (n : ℕ) (x : D.StateSpace) :
    exactGapValueReal * ‖finiteVacuumCentered D.vacuum x‖ ^ 2 ≤
      inner ℝ (D.hamiltonian n x) x := by
  rw [D.centeredNormSq_eq_gibbsVariance n x,
    D.hamiltonianQuadraticForm_eq_heatBathDirichlet n x]
  exact D.exactGapSingleLinkHeatBathPoincare n
    (D.observableRealization n x)

/-- Every excitation-sector eigenvalue inherits the public exact lower bound
from the concrete single-link Wilson heat-bath Poincare estimate. -/
theorem finite_wilson_single_link_heat_bath_restricted_eigenvalues_ge_exactGap
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData W)
    (n : ℕ) (i : Fin D.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        D.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          D.excitedFinrank i :=
  finite_wilson_vacuum_poincare_restricted_eigenvalues_ge_exactGap
    D.toVacuumPoincareGapData n i

end

end MathlibAnalytic
end MGAP4D
