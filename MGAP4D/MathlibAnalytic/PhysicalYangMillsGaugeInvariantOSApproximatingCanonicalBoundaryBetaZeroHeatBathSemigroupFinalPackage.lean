import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroSemigroupPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundaryBetaZeroFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryBetaZeroFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryBetaZeroFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryBetaZeroFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryBetaZeroFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryBetaZeroFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Public structural receipt for the complete finite-volume beta-zero
canonical boundary heat-bath dynamics. It packages the product-Haar
normalization, analyzed-range invariance, exact defect closure, ambient
intertwining, semigroup law, norm continuity, and generator derivative. -/
structure PeriodicHypercubicEvenCanonicalBoundaryBetaZeroStructuralPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop where
  boundaryFiberedGibbsDensity_eq_one :
    ∀ z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N),
      periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN 0 le_rfl z = 1
  boundaryVacuumMoment_eq_one :
    ∀ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
      periodicHypercubicEvenBoundaryVacuumMoment H N hN 0 le_rfl b = 1
  boundaryMarginal_eq_haar :
    periodicHypercubicEvenBoundaryMarginalMeasure H N hN 0 le_rfl =
      periodicHypercubicEvenBoundaryHaarMeasure H N
  generatorRangeInvariant :
    realHilbertIsometricAdjointCompressionGeneratorRangeInvariant
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN 0 le_rfl)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN 0 le_rfl).heatBathHamiltonianL2
  generatorDefect_eq_zero :
    periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
      H N hN 0 le_rfl = 0
  secondMomentDefect_eq_zero :
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
      H N hN 0 le_rfl = 0
  evolution_eq_boundaryExponential :
    ∀ t : ℝ,
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl t =
        realContinuousLinearOperatorExponentialSemigroup
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
            H N hN 0 le_rfl) t
  analysis_intertwines_evolution :
    ∀ (t : ℝ) (f : PeriodicHypercubicEvenBoundaryHaarL2 H N),
      periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN 0 le_rfl
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN 0 le_rfl t f) =
        ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN 0 le_rfl) t
          (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
            H N hN 0 le_rfl f)
  allRealTimeRangeInvariant :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN 0 le_rfl
  evolution_add :
    ∀ s t : ℝ,
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl (s + t) =
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN 0 le_rfl s *
          periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN 0 le_rfl t
  evolution_continuous :
    Continuous
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl)
  evolution_hasDerivAt :
    ∀ t : ℝ,
      HasDerivAt
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN 0 le_rfl)
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
            H N hN 0 le_rfl t *
          periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
            H N hN 0 le_rfl) t

/-- Public quantitative receipt for the beta-zero canonical boundary
Hamiltonian: exact compressed second moment, sharp Poincare constant one,
coercivity one on the vacuum-orthogonal sector, and exclusion of nonzero
vacuum-orthogonal zero modes. -/
structure PeriodicHypercubicEvenCanonicalBoundaryBetaZeroGapPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop where
  secondMoment_exact :
    realHilbertIsometricAdjointCompression
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN 0 le_rfl)
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 le_rfl).heatBathHamiltonianL2 *
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN 0 le_rfl).heatBathHamiltonianL2) =
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN 0 le_rfl *
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
          H N hN 0 le_rfl
  poincare_one :
    ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      ‖periodicHypercubicEvenCanonicalBoundaryVacuumCenteredL2
        H N hN 0 le_rfl f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN 0 le_rfl f) f
  coercive_one :
    ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN 0 le_rfl) f = 0 →
      ‖f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
            H N hN 0 le_rfl f) f
  vacuumOrthogonalKernel_eq_zero :
    ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN 0 le_rfl) f = 0 →
      periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
        H N hN 0 le_rfl f = 0 →
      f = 0

/-- Terminal public package combining the complete beta-zero boundary
semigroup with its sharp quantitative gap receipt. -/
structure PhysicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroHeatBathSemigroupFinalPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] : Prop where
  structural :
    PeriodicHypercubicEvenCanonicalBoundaryBetaZeroStructuralPackage H N hN
  quantitative :
    PeriodicHypercubicEvenCanonicalBoundaryBetaZeroGapPackage H N hN

/-- The complete finite-volume beta-zero canonical boundary heat-bath
semigroup and sharp gap package is realized without an additional range
invariance hypothesis. -/
theorem physicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroHeatBathSemigroupFinalPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)] :
    PhysicalYangMillsGaugeInvariantOSApproximatingCanonicalBoundaryBetaZeroHeatBathSemigroupFinalPackage
      H N hN := by
  refine ⟨?_, ?_⟩
  · refine
      { boundaryFiberedGibbsDensity_eq_one := ?_
        boundaryVacuumMoment_eq_one := ?_
        boundaryMarginal_eq_haar := ?_
        generatorRangeInvariant := ?_
        generatorDefect_eq_zero := ?_
        secondMomentDefect_eq_zero := ?_
        evolution_eq_boundaryExponential := ?_
        analysis_intertwines_evolution := ?_
        allRealTimeRangeInvariant := ?_
        evolution_add := ?_
        evolution_continuous := ?_
        evolution_hasDerivAt := ?_ }
    · intro z
      exact periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_betaZero
        H N hN z
    · intro b
      exact periodicHypercubicEvenBoundaryVacuumMoment_betaZero H N hN b
    · exact periodicHypercubicEvenBoundaryMarginalMeasure_betaZero H N hN
    · exact
        periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorRangeInvariant_betaZero
          H N hN
    · exact
        periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2_betaZero
          H N hN
    · exact
        periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_betaZero
          H N hN
    · intro t
      exact
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_betaZero
          H N hN t
    · intro t f
      exact
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply_betaZero
          H N hN t f
    · exact
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant_betaZero
          H N hN
    · intro s t
      exact
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add_betaZero
          H N hN s t
    · exact
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_continuous_betaZero
          H N hN
    · intro t
      exact
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_betaZero
          H N hN t
  · refine
      { secondMoment_exact := ?_
        poincare_one := ?_
        coercive_one := ?_
        vacuumOrthogonalKernel_eq_zero := ?_ }
    · exact periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMoment_betaZero
        H N hN
    · intro f
      exact
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_poincare_one_betaZero
          H N hN f
    · intro f hf
      exact
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_coercive_one_betaZero
          H N hN f hf
    · intro f hfOrth hfZero
      exact
        periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2_kernel_eq_zero_betaZero
          H N hN f hfOrth hfZero

end

end MathlibAnalytic
end MGAP4D