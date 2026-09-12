import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompressionQuadraticPackage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryZeroTimeIntertwining

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryHamiltonianNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryHamiltonianTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryHamiltonianCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryHamiltonianSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryHamiltonianMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryHamiltonianBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical boundary Hamiltonian obtained by compressing the actual
finite Wilson heat-bath Hamiltonian through boundary analysis and its Hilbert
adjoint synthesis. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  realHilbertIsometricAdjointCompression
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

@[simp] theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_apply
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta f =
      periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) :=
  rfl

/-- The boundary Hamiltonian quadratic form is exactly the actual Gibbs
heat-bath quadratic form of the analyzed boundary vector. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_quadraticForm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) f =
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) :=
  realHilbertIsometricAdjointCompression_quadraticForm
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    f

/-- The boundary Hamiltonian is symmetric in the real Hilbert pairing. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_inner_symm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) g =
      inner ℝ f
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta g) := by
  exact realHilbertIsometricAdjointCompression_inner_symm
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    (continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
    f g

/-- The canonical boundary heat-bath Hamiltonian is nonnegative. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta f) f := by
  exact realHilbertIsometricAdjointCompression_nonneg
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    (continuous_compact_oriented_heatBathHamiltonianL2_nonneg
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
    f

/-- The boundary Dirichlet form is the finite sum of actual local Gibbs
heat-bath fluctuation norms of the analyzed boundary vector. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_dirichletForm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) f =
      ∑ target :
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.geometry.Edge,
        ‖(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkHeatBathFluctuationL2
            target
            (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
              H N hN beta hbeta f)‖ ^ 2 := by
  rw [periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_quadraticForm]
  exact continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta f)

/-- The compressed boundary Hamiltonian annihilates the concrete OS boundary
vacuum exactly. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) = 0 := by
  apply realHilbertIsometricAdjointCompression_vacuum
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
  rw [periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum]
  exact continuous_compact_oriented_heatBathHamiltonianL2_vacuum
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)

/-- Vacuum centering on the concrete boundary Haar `L²` carrier. -/
def periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  f - inner ℝ
    (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f •
      periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta

/-- Canonical analysis commutes exactly with vacuum centering. -/
theorem periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuumCentered
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
          H N hN beta hbeta f) =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).vacuumCenteredL2
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) := by
  unfold periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [map_sub, map_smul,
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum,
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum_inner]

/-- The actual finite Wilson heat-bath Poincare inequality transfers without
loss to the canonical boundary Hamiltonian and boundary vacuum centering. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_poincare
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gap : ℝ)
    (hPoincare :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).HeatBathPoincareL2 gap)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    gap * ‖periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
      H N hN beta hbeta f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) f := by
  have h := hPoincare
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta f)
  rw [← periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuumCentered]
    at h
  rw [periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_quadraticForm]
  simpa using h

/-- Boundary vacuum centering fixes every vector orthogonal to the concrete
boundary vacuum. -/
theorem periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0) :
    periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
        H N hN beta hbeta f = f := by
  unfold periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
  rw [hf]
  simp

/-- The finite Wilson Poincare constant gives boundary Hamiltonian coercivity
on the concrete vacuum-orthogonal sector. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_coercive
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gap : ℝ)
    (hPoincare :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).HeatBathPoincareL2 gap)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0) :
    gap * ‖f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta f) f := by
  simpa [periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2_eq_self
    H N hN beta hbeta f hf] using
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_poincare
      H N hN beta hbeta gap hPoincare f

/-- A strictly positive finite Wilson Poincare constant excludes a nonzero
boundary-vacuum-orthogonal zero mode. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_kernel_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gap : ℝ) (hgap : 0 < gap)
    (hPoincare :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).HeatBathPoincareL2 gap)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hfOrth : inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0)
    (hfZero :
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta f = 0) :
    f = 0 := by
  have hcoercive :=
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_coercive
      H N hN beta hbeta gap hPoincare f hfOrth
  rw [hfZero, inner_zero_left] at hcoercive
  have hnormsq : ‖f‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖f‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)

/-- The boundary Hamiltonian maps the full boundary carrier into the
vacuum-orthogonal sector. -/
theorem periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_vacuum_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)
      (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN beta hbeta f) = 0 := by
  apply realHilbertIsometricAdjointCompression_range_orthogonal_to_vacuum
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
    (continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
    (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)
  rw [periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum]
  exact continuous_compact_oriented_heatBathHamiltonianL2_vacuum
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
