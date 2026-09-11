import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisApplyRawActualAnalysis
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisDerivedRayleighMass

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem analysisImageDerivedRayleighMassTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance analysisImageDerivedRayleighMassTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance analysisImageDerivedRayleighMassCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance analysisImageDerivedRayleighMassSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance analysisImageDerivedRayleighMassMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance analysisImageDerivedRayleighMassBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance analysisImageDerivedRayleighMassSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The canonical actual-Wilson analysis-range condition is exactly sufficient
for the explicit raw continuous analysis vector to lie in the same physical
positive-half range.  This removes the duplicate `hRawRange` frontier: the two
vectors are equal in Haar `L²` by the preceding Riesz--Fubini identification. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalf_range_of_analysisImage_mem_positiveHalf_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 analysisImageDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ) (c : Fin (k + 1) → ℝ)
    (hAnalysisRange : periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) 2 analysisImageDerivedRayleighMassTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c) ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
      (halfExtent n) (beta n) (hbeta n) k c ∈ (Q.positiveHalfL2LinearMap hInvariant n).range := by
  rw [← periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_normalizedTracePolynomial_eq_rawActualAnalysisHaarL2]
  simpa using hAnalysisRange

/-- Consequently the variational mass of the reconstructed closed OS
Hamiltonian is nonnegative from the canonical actual-analysis range condition
alone; no separate raw-analysis range hypothesis is needed. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_analysisImage_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback S D halfExtent 2 analysisImageDerivedRayleighMassTwoRankPositive beta hbeta)
    (hInvariant : ∀ n, D.WeakStarReflectionInvariant (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility Q hInvariant)
    (n k : ℕ) (c : Fin (k + 1) → ℝ) (hH : 1 < halfExtent n) (hbetaPos : 0 < beta n) (hc : c ≠ 0)
    (hzero : inner ℝ (periodicHypercubicEvenBoundaryMarginalVacuumL2 (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2 (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hAnalysisRange : periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) 2 analysisImageDerivedRayleighMassTwoRankPositive (beta n) (hbeta n)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2 (halfExtent n) (beta n) (hbeta n) k c) ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range)
    (T : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData S D halfExtent 2
      analysisImageDerivedRayleighMassTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : 0 ≤ T.physicalYangMillsMass := by
  have hRawRange :=
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalf_range_of_analysisImage_mem_positiveHalf_range
      hInvariant n k c hAnalysisRange
  exact Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_range
    hInvariant U n k c hH hbetaPos hc hzero hRawRange T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
