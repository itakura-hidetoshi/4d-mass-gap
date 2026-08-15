import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerFiniteRangeBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerSupportRangeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerSupportRangeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerSupportRangeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerSupportRangeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerSupportRangeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerSupportRangeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerSupportRangeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerSupportRangeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance normalizedTracePowerSupportRangeBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance normalizedTracePowerSupportRangeOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerSupportRangePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerSupportRangeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 normalizedTracePowerSupportRangeTwoRankPositive beta hbeta
    Q.toWeakStarBridge hInvariant n

/-- Only trace powers with nonzero polynomial coefficient need a physical
range realization.  Zero-coefficient powers contribute the zero vector, which
belongs to every linear-map range.  Thus the model-facing realization
obligation is exactly the coefficient support of the chosen finite polynomial,
not all powers up to its formal degree. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_powerActualAnalysis_mem_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerSupportRangeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_eq_sum_powerActualAnalysis]
  exact (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)).sum_mem fun j _hj => by
    by_cases hcj : c j = 0
    · simp [hcj]
    · exact
        (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)).smul_mem (c j)
          (hPowerRange j hcj)

/-- The support-indexed exact range statement immediately gives the range
closure required by the reconstructed physical-excitation machinery. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_support_powerActualAnalysis_mem_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerSupportRangeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  exact subset_closure
    (Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_support_powerActualAnalysis_mem_range
      n k c hPowerRange)

/-- The remaining finite model-facing realization obligation can therefore be
fed directly into the already-established reconstructed Hamiltonian route.
No density assumption, global pullback surjectivity, universal plaquette-algebra
lift, new positivity hypothesis, or new Hamiltonian hypothesis is introduced. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_powerActualAnalysis_mem_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerSupportRangeTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hH : 1 < halfExtent n)
    (hbetaPos : 0 < beta n)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2
          (halfExtent n) (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hPowerRange : ∀ j : Fin (k + 1), c j ≠ 0 →
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n))
    (T : (normalizedTracePowerSupportRangePreHilbert Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  have hClosure :=
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_support_powerActualAnalysis_mem_range
      n k c hPowerRange
  exact
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveTimeRangeClosure
      hInvariant U n k c hH hbetaPos hc hzero hClosure T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
