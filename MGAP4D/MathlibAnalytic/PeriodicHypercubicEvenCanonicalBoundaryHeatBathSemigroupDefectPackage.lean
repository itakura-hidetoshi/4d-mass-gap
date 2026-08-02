import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompressionSemigroupDefect
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectPackage

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance canonicalBoundarySemigroupDefectNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundarySemigroupDefectTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundarySemigroupDefectCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundarySemigroupDefectSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundarySemigroupDefectMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundarySemigroupDefectBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The positive second-moment curvature of the actual finite Wilson
heat-bath Hamiltonian after canonical boundary compression. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  realHilbertIsometricAdjointCompressionSecondMomentDefect
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

/-- Exact operator decomposition of the compressed ambient Hamiltonian square
into the square of the boundary Hamiltonian and the positive leakage
curvature. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMoment_decomposition
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    realHilbertIsometricAdjointCompression
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
          H N hN beta hbeta := by
  exact realHilbertIsometricAdjointCompression_secondMoment_decomposition
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2

/-- The second-moment curvature quadratic form is exactly the squared norm of
the concrete finite Wilson generator leakage. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_quadraticForm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
          H N hN beta hbeta f) f =
      inner ℝ
        (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta f)
        (periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
          H N hN beta hbeta f) := by
  exact
    realHilbertIsometricAdjointCompressionSecondMomentDefect_quadraticForm
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
      (continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
      f

/-- The finite Wilson boundary second-moment curvature is nonnegative. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
        H N hN beta hbeta f) f := by
  rw [periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_quadraticForm]
  exact real_inner_self_nonneg

/-- Exact preservation of the Hamiltonian second moment is equivalent to
vanishing of the full finite Wilson boundary generator leakage. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_eq_zero_iff_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
        H N hN beta hbeta = 0 ↔
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0 := by
  exact
    realHilbertIsometricAdjointCompressionSecondMomentDefect_eq_zero_iff_generatorDefect_eq_zero
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
      (continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))

/-- Any concrete boundary observable with nonzero generator leakage is already
a witness that the compressed full heat-bath evolution cannot be generated by
only the square of the compressed Hamiltonian. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2_ne_zero_of_generatorDefect_apply_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N)
    (hf : periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
      H N hN beta hbeta f ≠ 0) :
    periodicHypercubicEvenCanonicalBoundaryHeatBathSecondMomentDefectL2
      H N hN beta hbeta ≠ 0 := by
  exact
    realHilbertIsometricAdjointCompressionSecondMomentDefect_ne_zero_of_generatorDefect_apply_ne_zero
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
      (continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta))
      f hf

/-- The canonical bounded boundary generator matching the normalization of the
full heat-bath exponential. -/
noncomputable def
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  (-(1 / 2 : ℝ)) •
    periodicHypercubicEvenCanonicalBoundaryHeatBathHamiltonianL2
      H N hN beta hbeta

/-- Compression of the ambient full heat-bath generator is exactly the
canonical boundary full generator. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2_compression
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    realHilbertIsometricAdjointCompression
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta)
        (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)) =
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
        H N hN beta hbeta := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
  unfold periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
  rw [realHilbertIsometricAdjointCompression_smul]

/-- Zero Hamiltonian leakage implies zero leakage for the normalized full
heat-bath generator. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorDefectL2_eq_zero_of_heatBathGeneratorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0) :
    realHilbertIsometricAdjointCompressionGeneratorDefect
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta)
        (ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)) = 0 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathGeneratorL2
  exact
    realHilbertIsometricAdjointCompressionGeneratorDefect_smul_eq_zero
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).heatBathHamiltonianL2
      hDefect (-(1 / 2 : ℝ))

/-- Under the isolated zero-leakage condition, the canonical compressed full
heat-bath evolution is exactly the exponential of the boundary Hamiltonian. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_of_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0)
    (t : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta t =
      realContinuousLinearOperatorExponentialSemigroup
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
          H N hN beta hbeta) t := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN beta hbeta
  have hGeneratorDefect :
      realHilbertIsometricAdjointCompressionGeneratorDefect A
        C.fullHeatBathGeneratorL2 = 0 := by
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorDefectL2_eq_zero_of_heatBathGeneratorDefect_eq_zero
        H N hN beta hbeta hDefect
  have hExp :=
    realHilbertIsometricAdjointCompression_exponential_of_generatorDefect_eq_zero
      A C.fullHeatBathGeneratorL2 hGeneratorDefect t
  unfold periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
  unfold ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
  unfold realContinuousLinearOperatorExponentialSemigroup
  rw [hExp,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2_compression]

/-- Zero generator leakage gives exact ambient-boundary intertwining at every
real heat-bath time. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply_of_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0)
    (t : ℝ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t f) =
      ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta)
        t
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN beta hbeta
  have hGeneratorDefect :
      realHilbertIsometricAdjointCompressionGeneratorDefect A
        C.fullHeatBathGeneratorL2 = 0 := by
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorDefectL2_eq_zero_of_heatBathGeneratorDefect_eq_zero
        H N hN beta hbeta hDefect
  have hExp :=
    realHilbertIsometricAdjointCompression_exponential_analysis_apply_of_generatorDefect_eq_zero
      A C.fullHeatBathGeneratorL2 hGeneratorDefect t f
  simpa [C, A,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2,
    ContinuousCompactOrientedGaugeWilsonSystem.fullHeatBathEvolutionRealL2,
    realContinuousLinearOperatorExponentialSemigroup,
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2_compression]
    using hExp.symm

/-- The generator zero-leakage condition discharges the former all-time
analyzed-range invariance obligation. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant_of_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant
      H N hN beta hbeta := by
  intro t f
  refine ⟨
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
      H N hN beta hbeta t f, ?_⟩
  exact
    (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_analysis_apply_of_generatorDefect_eq_zero
      H N hN beta hbeta hDefect t f).symm

/-- Consequently, zero generator leakage makes the compressed boundary family
an exact real-time semigroup without a separate range hypothesis. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add_of_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0)
    (s t : ℝ) :
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta (s + t) =
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta s *
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t := by
  exact periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_add
    H N hN beta hbeta
    (periodicHypercubicEvenCanonicalBoundaryFullHeatBathRangeInvariant_of_generatorDefect_eq_zero
      H N hN beta hbeta hDefect)
    s t

/-- Under zero leakage, the complete boundary family is continuous in operator
norm because it is the exponential of its bounded boundary generator. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_continuous_of_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0) :
    Continuous
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta) := by
  have hfun :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta =
        realContinuousLinearOperatorExponentialSemigroup
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
            H N hN beta hbeta) := by
    funext t
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_of_generatorDefect_eq_zero
        H N hN beta hbeta hDefect t
  rw [hfun]
  exact continuous_realContinuousLinearOperatorExponentialSemigroup
    (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
      H N hN beta hbeta)

/-- Under zero leakage, the operator-norm derivative exists at every real time
and is generated by the compressed boundary Hamiltonian. -/
theorem
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_hasDerivAt_of_generatorDefect_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hDefect :
      periodicHypercubicEvenCanonicalBoundaryHeatBathGeneratorDefectL2
        H N hN beta hbeta = 0)
    (t : ℝ) :
    HasDerivAt
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN beta hbeta)
      (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta t *
        periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
          H N hN beta hbeta) t := by
  have hfun :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
          H N hN beta hbeta =
        realContinuousLinearOperatorExponentialSemigroup
          (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
            H N hN beta hbeta) := by
    funext u
    exact
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2_eq_boundaryExponential_of_generatorDefect_eq_zero
        H N hN beta hbeta hDefect u
  rw [hfun]
  exact realContinuousLinearOperatorExponentialSemigroup_hasDerivAt
    (periodicHypercubicEvenCanonicalBoundaryFullHeatBathGeneratorL2
      H N hN beta hbeta) t

end

end MathlibAnalytic
end MGAP4D
