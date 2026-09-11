import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryHeatBathSemigroupDefectPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundarySemigroupDefectFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundarySemigroupDefectFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundarySemigroupDefectFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundarySemigroupDefectFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundarySemigroupDefectFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundarySemigroupDefectFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Public unconditional package: the compressed ambient Hamiltonian square
splits into the boundary Hamiltonian square plus a positive curvature whose
quadratic form is exactly the generator-leakage energy.  Vanishing of this
curvature is equivalent to the complete generator range condition. -/
theorem
    physical_yang_mills_gauge_invariant_os_approximating_canonical_boundary_heatBath_secondMoment_defect_package
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (realHilbertIsometricAdjointCompression
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta)
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2 *
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2) =
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta *
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN beta hbeta +
        periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
          H N hN beta hbeta) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
            H N hN beta hbeta f) f =
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f)
          (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
            H N hN beta hbeta f)) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      0 ≤ inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
          H N hN beta hbeta f) f) ∧
    (periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
        H N hN beta hbeta = 0 ↔
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0) := by
  refine ⟨
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMoment_decomposition
      H N hN beta hbeta,
    ?_, ?_,
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_eq_zero_iff_generatorDefect_eq_zero
      H N hN beta hbeta⟩
  · intro f
    exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_quadraticForm
        H N hN beta hbeta f
  · intro f
    exact
      periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_nonneg
        H N hN beta hbeta f

/-- Public conditional closure package: once the now-isolated concrete
second-moment/generator leakage vanishes, the full finite Wilson heat-bath
evolution intertwines exactly with the boundary carrier, equals the exponential
of the compressed boundary Hamiltonian, preserves the analyzed range, and is
an operator-norm continuous differentiable real-time semigroup. -/
theorem
    physical_yang_mills_gauge_invariant_os_approximating_canonical_boundary_heatBath_zero_defect_dynamics_package
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0) :
    (∀ t : ℝ,
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t =
        realContinuousLinearOperatorExponentialSemigroup
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
            H N hN beta hbeta) t) ∧
    (∀ (t : ℝ) (f : PeriodicHypercubicEvenBoundaryHaarL2 H N),
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta t f) =
        ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
          t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta f)) ∧
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN beta hbeta ∧
    (∀ s t : ℝ,
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta (s + t) =
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta s *
          periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta t) ∧
    Continuous
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta) ∧
    (∀ t : ℝ,
      HasDerivAt
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta)
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta t *
          periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
            H N hN beta hbeta) t) := by
  refine ⟨?_, ?_,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant_of_generatorDefect_eq_zero
      H N hN beta hbeta hDefect,
    ?_,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_continuous_of_generatorDefect_eq_zero
      H N hN beta hbeta hDefect,
    ?_⟩
  · intro t
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_of_generatorDefect_eq_zero
        H N hN beta hbeta hDefect t
  · intro t f
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply_of_generatorDefect_eq_zero
        H N hN beta hbeta hDefect t f
  · intro s t
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add_of_generatorDefect_eq_zero
        H N hN beta hbeta hDefect s t
  · intro t
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_of_generatorDefect_eq_zero
        H N hN beta hbeta hDefect t

end

end MathlibAnalytic
end MGAP4D
