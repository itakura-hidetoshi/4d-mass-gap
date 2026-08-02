import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryFullHeatBathSemigroupPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryFullFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryFullFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryFullFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryFullFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryFullFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryFullFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Complete unconditional structural package for the canonical boundary
compression of the actual finite Wilson full heat-bath evolution: full-space
identity at time zero, exact vacuum preservation, the strong Hamiltonian
generator, and agreement with the preceding centered compression on the
vacuum-orthogonal sector. -/
theorem
    physical_yang_mills_gauge_invariant_os_approximating_canonical_boundary_full_heat_bath_structural_package
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta 0 = 1 ∧
    (∀ t : ℝ,
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t
          (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) =
        periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) ∧
    (∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      HasDerivAt
        (fun t : ℝ =>
          periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta t f)
        (-(1 / 2 : ℝ) •
          periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN beta hbeta f) 0) ∧
    (∀ (t : NNReal) (f : PeriodicHypercubicEvenBoundaryHaarL2 H N),
      inner ℝ
          (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f = 0 →
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta (t : ℝ) f =
        periodicHypercubicEvenCanonicalBoundaryCompressedHeatBathEvolutionL2
          H N hN beta hbeta t f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_zero
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_vacuum
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_zero
        H N hN beta hbeta
  · intro t f hf
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_centered_of_orthogonal
        H N hN beta hbeta t f hf

/-- Complete conditional dynamics package.  The single explicit
model-specific input is invariance of the canonically analyzed boundary range;
under that condition the adjoint compression is an honest real-time semigroup,
intertwines exactly with the actual finite Wilson Gibbs evolution, and is
uniquely characterized by that intertwining. -/
theorem
    physical_yang_mills_gauge_invariant_os_approximating_canonical_boundary_full_heat_bath_semigroup_package
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hRange : periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN beta hbeta) :
    (∀ s t : ℝ,
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta (s + t) =
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta s *
          periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta t) ∧
    (∀ (t : ℝ) (f : PeriodicHypercubicEvenBoundaryHaarL2 H N),
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN beta hbeta t f) =
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).
            fullHeatBathEvolutionRealL2 t
            (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
              H N hN beta hbeta f)) ∧
    (∀ (t : ℝ)
      (B : PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenBoundaryHaarL2 H N),
      (∀ f,
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).
            fullHeatBathEvolutionRealL2 t
            (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
              H N hN beta hbeta f) =
          periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN beta hbeta (B f)) →
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t = B) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add
        H N hN beta hbeta hRange
  · exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply
        H N hN beta hbeta hRange
  · intro t B hintertwine
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_of_intertwines
        H N hN beta hbeta t B hintertwine

end

end MathlibAnalytic
end MGAP4D
