import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryTemporalCompanionOpenHalfDegreeProbeNonzero

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private theorem positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

/-- The protected positive-degree witness on the interacting boundary and its
actual Wilson-analysis realization may be chosen with the *same* Fock dual
probe `q`, and that transported open-half probe is a nonzero Haar `L²` vector.

This strengthens the existing transport/limit package without changing its
polynomial, degree, measure, strict protected Gram inequality, or limiting
matrix coefficient.  The only new conclusion is the cancellation-independent
fact that the actual target probe itself is nonzero. -/
theorem
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_actualBoundaryHaarTransport_protectedGram_nonzeroProbe_and_analysisLimit
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta.le)
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          H beta hbeta.le k c) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H (i : ℕ)).FeatureHilbert,
        (∫ b, inner ℝ q
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
              H (i : ℕ)).feature b)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
            positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
            beta hbeta.le)) ≠ 0 ∧
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
            H (i : ℕ) q ≠ 0 ∧
        0 < ((Real.exp (-beta)) ^
          (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta (i : ℕ)) *
          (∫ b₁, ∫ b₂, inner ℝ
            (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
              H k c (i : ℕ) b₁)
            (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
              H k c (i : ℕ) b₂)
            ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
              positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
              beta hbeta.le)
            ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
              positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
              beta hbeta.le)) ∧
        periodicHypercubicEvenBoundaryHaarToMarginalL2
            H 2 positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
            beta hbeta.le
            (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
              H beta hbeta.le k c) =
          periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
            H beta hbeta.le k c ∧
        ‖periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta.le k c‖ =
          ‖periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
            H beta hbeta.le k c‖ ∧
        inner ℝ
          (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta.le)
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta.le k c) = 0 ∧
        Tendsto
          (fun degree =>
            periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
              H (i : ℕ) beta hbeta.le degree
              (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
                H beta hbeta.le k c) q)
          atTop
          (𝓝 (inner ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
              H (i : ℕ) q)
            (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
              H 2 positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
              beta hbeta.le
              (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
                H beta hbeta.le k c)))) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_actualBoundaryHaarTransport_protectedGram_and_analysisLimit
      H hH beta hbeta k c hc hzero with
    ⟨i, hi, q, hq, hstrict, htransport, hnorm, hcenter, hlimit⟩
  have hq' :
      (∫ b, inner ℝ q
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
            H (i : ℕ)).feature b)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
          positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
          beta hbeta.le)) ≠ 0 := by
    simpa only using hq
  have hprobe :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
        H (i : ℕ) q ≠ 0 :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_ne_zero_of_weighted_boundary_integral_ne_zero
      H (i : ℕ) hH q
      (periodicHypercubicEvenBoundaryMarginalMeasure H 2
        positiveBoundaryTemporalWilsonActualAnalysisProbeNonzeroTwoRankPositive
        beta hbeta.le)
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c)
      hq'
  refine ⟨i, hi, q, hq', hprobe, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only using hstrict
  · simpa only using htransport
  · exact hnorm
  · exact hcenter
  · simpa only using hlimit

end

end MathlibAnalytic
end MGAP4D