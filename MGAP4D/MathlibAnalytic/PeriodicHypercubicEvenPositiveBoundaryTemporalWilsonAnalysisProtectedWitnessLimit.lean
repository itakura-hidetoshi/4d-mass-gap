import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedStrictness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonAnalysisAdjointProductLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private theorem positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The same positive-degree dual probe that gives a strictly positive
protected four-edge Fock component inside the literal full positive-boundary
Wilson sector also feeds the genuine full-independent four-edge Hilbert-adjoint
approximation converging to the actual Wilson boundary Gram analysis matrix
coefficient.

This theorem deliberately does not infer that the limiting matrix coefficient
is nonzero: it aligns the cancellation-free strict component and the actual
analysis limit without assuming marginal-transport-defect vanishing or
replacing the full independent Taylor/Fock family by a diagonal truncation. -/
theorem periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeGram_pos_and_fourEdgeWilsonAnalysisLimit_of_cyclicDualProbe
    {H : ℕ} (hH : 0 < H) (beta : ℝ) (hbeta : 0 < beta)
    (k n : ℕ) (c : Fin (k + 1) → ℝ)
    (q : (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature H n).FeatureHilbert)
    (hq : (∫ b, inner ℝ q
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature H n).feature b)
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
        positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitTwoRankPositive beta hbeta.le)) ≠ 0) :
    0 < ((Real.exp (-beta)) ^
      (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
      specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta n) *
      (∫ b₁, ∫ b₂, inner ℝ
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₁)
        (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature H k c n b₂)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitTwoRankPositive beta hbeta.le)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitTwoRankPositive beta hbeta.le)) ∧
    ∀ f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2),
      Tendsto
        (fun degree =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
            H n beta hbeta.le degree f q)
        atTop
        (𝓝 (inner ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2 H n q)
          (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator H 2
            positiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimitTwoRankPositive
            beta hbeta.le f))) := by
  constructor
  · exact
      periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeGram_pos_of_cyclicDualProbe
        H beta hbeta k n c q hq
  · intro f
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral_tendsto_inner_analysis
        hH n beta hbeta.le f q

end

end MathlibAnalytic
end MGAP4D
