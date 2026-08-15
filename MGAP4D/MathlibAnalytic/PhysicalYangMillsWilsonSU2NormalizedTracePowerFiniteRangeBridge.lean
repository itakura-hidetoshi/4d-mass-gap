import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisApplyRawActualAnalysis
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeSubmoduleRangeClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerFiniteRangeBridgeTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerFiniteRangeBridgeNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerFiniteRangeBridgeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerFiniteRangeBridgeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerFiniteRangeBridgeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerFiniteRangeBridgeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerFiniteRangeBridgeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerFiniteRangeBridgeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance normalizedTracePowerFiniteRangeBridgeBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance normalizedTracePowerFiniteRangeBridgeOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- One normalized-trace power on the interacting boundary marginal, transported
by the already-constructed square-root-vacuum linear isometry to the boundary
Haar `L²` carrier used by the actual Wilson analysis operator. -/
noncomputable def periodicHypercubicEvenBoundaryNormalizedTracePowerHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (j : ℕ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H 2 :=
  periodicHypercubicEvenBoundaryMarginalToHaarL2
    H 2 normalizedTracePowerFiniteRangeBridgeTwoRankPositive beta hbeta
    (ContinuousMap.toLp (E := ℝ) 2
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 normalizedTracePowerFiniteRangeBridgeTwoRankPositive beta hbeta) ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^ j))

/-- The actual open-half `L²` analysis image of one vacuum-transported
normalized-trace power.  These are the finite family whose physical range
realization suffices for every polynomial of bounded degree. -/
noncomputable def periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (j : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
  periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H 2 normalizedTracePowerFiniteRangeBridgeTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryNormalizedTracePowerHaarL2
      H beta hbeta j)

/-- The transported normalized-trace polynomial is exactly the finite linear
combination of the transported trace-power vectors.  This is only linearity of
the existing marginal-to-Haar isometry. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_eq_sum_powerHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        H beta hbeta k c =
      ∑ j : Fin (k + 1), c j •
        periodicHypercubicEvenBoundaryNormalizedTracePowerHaarL2
          H beta hbeta (j : ℕ) := by
  unfold periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
  unfold periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  rfl

/-- Applying the actual Wilson boundary analysis operator to a normalized-trace
polynomial is therefore the same finite linear combination of the individual
trace-power analysis images. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_normalizedTracePolynomial_eq_sum_powerActualAnalysis
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 normalizedTracePowerFiniteRangeBridgeTwoRankPositive beta hbeta
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta k c) =
      ∑ j : Fin (k + 1), c j •
        periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          H beta hbeta (j : ℕ) := by
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_eq_sum_powerHaarL2]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  rfl

/-- The explicit raw actual-analysis `L²` mode itself is the same finite sum.
The nontrivial analytic identification `A_φ f = g_raw` is reused from the
existing Riesz--Fubini theorem. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_eq_sum_powerActualAnalysis
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        H beta hbeta k c =
      ∑ j : Fin (k + 1), c j •
        periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          H beta hbeta (j : ℕ) := by
  rw [← periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_normalizedTracePolynomial_eq_rawActualAnalysisHaarL2]
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_normalizedTracePolynomial_eq_sum_powerActualAnalysis
      H beta hbeta k c

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- For a degree-`k` normalized-trace polynomial it is enough to realize the
`k+1` explicit vacuum-transported trace-power analysis images in the existing
physical positive-time `L²` range.  Linearity then places the full raw
actual-analysis mode in the range exactly, not merely in its closure.

This is strictly more target-specific than lifting the whole universal actual
plaquette algebra, and it introduces no density or surjectivity statement. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_powerActualAnalysis_mem_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerFiniteRangeBridgeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerRange : ∀ j : Fin (k + 1),
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  choose F hF using hPowerRange
  refine ⟨∑ j : Fin (k + 1), c j • F j, ?_⟩
  rw [map_sum]
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2_eq_sum_powerActualAnalysis]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, hF j]

/-- Consequently the same finite family of exact range statements supplies the
range-closure input consumed by the reconstructed physical-excitation route. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2RangeClosure_of_powerActualAnalysis_mem_range
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerFiniteRangeBridgeTwoRankPositive beta hbeta)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hPowerRange : ∀ j : Fin (k + 1),
      periodicHypercubicEvenBoundaryNormalizedTracePowerActualAnalysisHaarL2
          (halfExtent n) (beta n) (hbeta n) (j : ℕ) ∈
        LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n)) := by
  exact subset_closure
    (Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_powerActualAnalysis_mem_range
      n k c hPowerRange)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
