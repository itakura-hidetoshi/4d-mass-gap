import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolution
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryDynamicsPackageNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryDynamicsPackageTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryDynamicsPackageCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryDynamicsPackageSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryDynamicsPackageMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryDynamicsPackageBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The complete finite-volume canonical boundary heat-bath dynamics package:
Hamiltonian symmetry and nonnegativity, exact vacuum zero energy, range
orthogonality, local Dirichlet-form representation, and zero-time centered
evolution are exposed together from the actual finite Wilson Gibbs system. -/
theorem
    physical_yang_mills_gauge_invariant_os_approximating_canonical_boundary_heat_bath_dynamics_package
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∀ f g : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) g =
        inner ℝ f
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta g)) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      0 ≤ inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) f) ∧
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) = 0 ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) = 0) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) f =
        ∑ target :
            (periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.geometry.Edge,
          ‖(periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).
                singleLinkHeatBathFluctuationL2 target
              (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
                H N hN beta hbeta f)‖ ^ 2) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0 →
      periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
          H N hN beta hbeta 0 f = f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_inner_symm
      H N hN beta hbeta
  · exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_nonneg
      H N hN beta hbeta
  · exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_vacuum
      H N hN beta hbeta
  · exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_vacuum_inner
      H N hN beta hbeta
  · exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_dirichletForm
      H N hN beta hbeta
  · intro f hf
    exact
      periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2_zero_of_orthogonal
        H N hN beta hbeta f hf

/-- The quantitative part of the package: an actual finite Wilson heat-bath
Poincare inequality transfers to the boundary-centered Poincare estimate,
coercivity on the vacuum-orthogonal sector, and absence of nonzero
vacuum-orthogonal zero modes when the gap is positive. -/
theorem
    physical_yang_mills_gauge_invariant_os_approximating_canonical_boundary_heat_bath_gap_package
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gap : ℝ)
    (hPoincare :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).
          HeatBathPoincareL2 gap) :
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      gap * ‖periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
        H N hN beta hbeta f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) f) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
          (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0 →
      gap * ‖f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) f) ∧
    (0 < gap →
      ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        inner ℝ
            (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0 →
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f = 0 →
        f = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_poincare
      H N hN beta hbeta gap hPoincare
  · intro f hf
    exact periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_coercive
      H N hN beta hbeta gap hPoincare f hf
  · intro hgap f hfOrth hfZero
    exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_kernel_eq_zero
        H N hN beta hbeta gap hgap hPoincare f hfOrth hfZero

end

end MathlibAnalytic
end MGAP4D
