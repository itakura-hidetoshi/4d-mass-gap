import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHilbertEquivalence
import MGAP4D.MathlibAnalytic.FiniteWilsonSingleLinkHeatBathHamiltonianBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Hamiltonian data on the canonical Euclidean Gibbs Hilbert realization of a
fixed finite Wilson system.

The Hilbert carrier, normalized vacuum, observable realization, and the
centered-norm/Gibbs-variance identity are no longer supplied as independent
inputs.  They are generated canonically from the finite Wilson Gibbs law.  The
remaining analytic obligation is the identification of the Hamiltonian
quadratic form with the exact single-link heat-bath Dirichlet form. -/
structure FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (i : W.index) where
  hamiltonian :
    ℕ → (W.system i).GibbsHilbertSpace →ₗ[ℝ]
      (W.system i).GibbsHilbertSpace
  hamiltonianSymmetric :
    ∀ n : ℕ, (hamiltonian n).IsSymmetric
  vacuumEnergyZero :
    ∀ n : ℕ,
      hamiltonian n (W.system i).gibbsHilbertVacuum = 0
  hamiltonianQuadraticForm_eq_heatBathDirichlet :
    ∀ (n : ℕ) (x : (W.system i).GibbsHilbertSpace),
      inner ℝ (hamiltonian n x) x =
        (W.system i).singleLinkHeatBathDirichletForm
          ((W.system i).gibbsHilbertObserveLinearMap x)
  exactGapSingleLinkHeatBathPoincare :
    (W.system i).ExactGapSingleLinkHeatBathPoincare
  ExcitedDimension : ℕ
  excitedFinrank :
    Module.finrank ℝ
        (finiteVacuumOrthogonal (W.system i).gibbsHilbertVacuum) =
      ExcitedDimension

/-- Fill the general finite Wilson Hamiltonian bridge with the canonical Gibbs
Hilbert carrier at the fixed lattice scale `i`. -/
noncomputable def
    FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData.toHamiltonianBridgeData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {i : W.index}
    (D : FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData W i) :
    FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData W :=
  { StateSpace := (W.system i).GibbsHilbertSpace
    stateNormedAddCommGroup := inferInstance
    stateInnerProductSpace := inferInstance
    stateFiniteDimensional := inferInstance
    vacuum := (W.system i).gibbsHilbertVacuum
    vacuum_norm := finite_lattice_gibbsHilbertVacuum_norm (W.system i)
    hamiltonian := D.hamiltonian
    hamiltonianSymmetric := D.hamiltonianSymmetric
    vacuumEnergyZero := D.vacuumEnergyZero
    scale := fun _n => i
    observableRealization := fun _n =>
      (W.system i).gibbsHilbertObserveLinearMap
    centeredNormSq_eq_gibbsVariance := by
      intro _n x
      exact finite_lattice_gibbsHilbert_vacuumCentered_norm_sq_observe
        (W.system i) x
    hamiltonianQuadraticForm_eq_heatBathDirichlet :=
      D.hamiltonianQuadraticForm_eq_heatBathDirichlet
    exactGapSingleLinkHeatBathPoincare := fun _n =>
      D.exactGapSingleLinkHeatBathPoincare
    ExcitedDimension := D.ExcitedDimension
    excitedFinrank := D.excitedFinrank }

/-- The canonical finite Wilson Gibbs Hilbert realization generates the
vacuum-centered Hamiltonian Poincare package without an external
centered-norm/variance bridge assumption. -/
noncomputable def
    FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData.toVacuumPoincareGapData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {i : W.index}
    (D : FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData W i) :
    FiniteWilsonVacuumPoincareHamiltonianGapData :=
  D.toHamiltonianBridgeData.toVacuumPoincareGapData

/-- The concrete Gibbs Hilbert realization turns the exact single-link
heat-bath Poincare estimate into the global vacuum-centered Hamiltonian
Poincare inequality. -/
theorem finite_wilson_concrete_gibbs_hilbert_implies_vacuum_poincare
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {i : W.index}
    (D : FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData W i)
    (n : ℕ) (x : (W.system i).GibbsHilbertSpace) :
    exactGapValueReal *
        ‖finiteVacuumCentered (W.system i).gibbsHilbertVacuum x‖ ^ 2 ≤
      inner ℝ (D.hamiltonian n x) x :=
  finite_wilson_single_link_heat_bath_implies_vacuum_poincare
    D.toHamiltonianBridgeData n x

/-- Every excitation-sector eigenvalue in the canonical Gibbs Hilbert
realization inherits the public exact lower bound. -/
theorem
    finite_wilson_concrete_gibbs_hilbert_restricted_eigenvalues_ge_exactGap
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {i : W.index}
    (D : FiniteWilsonConcreteGibbsHilbertHamiltonianBridgeData W i)
    (n : ℕ) (j : Fin D.ExcitedDimension) :
    exactGapValueReal ≤
      (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
        D.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
          D.excitedFinrank j :=
  finite_wilson_single_link_heat_bath_restricted_eigenvalues_ge_exactGap
    D.toHamiltonianBridgeData n j

end

end MathlibAnalytic
end MGAP4D
