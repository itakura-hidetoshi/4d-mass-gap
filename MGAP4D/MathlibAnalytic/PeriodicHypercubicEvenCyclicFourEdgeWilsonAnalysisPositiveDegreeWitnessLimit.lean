import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockDualProbe
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonAnalysisAdjointProductLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private theorem cyclicFourEdgePositiveDegreeWitnessLimitTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgePositiveDegreeWitnessLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgePositiveDegreeWitnessLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgePositiveDegreeWitnessLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgePositiveDegreeWitnessLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgePositiveDegreeWitnessLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgePositiveDegreeWitnessLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A centered nonzero boundary polynomial supplies one strictly positive
Taylor/Fock degree and one dual feature vector that are simultaneously valid
for the actual full rectangular four-edge Wilson adjoint approximation.

The first conclusion is the already-proved nonzero interacting-boundary
marginal moment.  The second conclusion only aligns the same degree and dual
vector with the exact Wilson-analysis limit; it deliberately does not infer
that the limit is nonzero and does not assume the marginal transport defect
vanishes. -/
theorem
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_dualProbe_with_fourEdgeWilsonAnalysisLimit
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgePositiveDegreeWitnessLimitTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 cyclicFourEdgePositiveDegreeWitnessLimitTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      0 < beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ) ∧
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H (i : ℕ)).FeatureHilbert,
        (∫ b,
          inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H (i : ℕ)).feature b)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFourEdgePositiveDegreeWitnessLimitTwoRankPositive beta hbeta.le)) ≠ 0 ∧
        ∀ f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2),
          Tendsto
            (fun degree =>
              periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
                H (i : ℕ) beta hbeta.le degree f q)
            atTop
            (𝓝
              (inner ℝ
                (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
                  H (i : ℕ) q)
                (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
                  H 2 cyclicFourEdgePositiveDegreeWitnessLimitTwoRankPositive
                  beta hbeta.le f))) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_dualFeatureProbe
      H beta hbeta k c hc hzero with
    ⟨i, hi, hTaylor, q, hq⟩
  refine ⟨i, hi, hTaylor, q, hq, ?_⟩
  intro f
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral_tendsto_inner_analysis
      hH (i : ℕ) beta hbeta.le f q

end

end MathlibAnalytic
end MGAP4D
