import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonActualAnalysisProbeNonzero

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private theorem positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A strict quadratic witness for the canonical completed actual Wilson
factorization `A† A` is a cancellation-free witness that the genuine analysis
output is nonzero.  This reuses the generic factorized operator rather than
introducing an SU(2)-specific duplicate. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_factorized_inner_self_pos
    {H : ℕ}
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (hpos :
      0 < inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
          beta hbeta f)
        f) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
        beta hbeta f ≠ 0 := by
  intro hzero
  have h := hpos
  rw [
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self,
    hzero, norm_zero] at h
  norm_num at h

/-- It is enough to exhibit one strict quadratic witness for the canonical
`A† A` factorization to prove that the completed actual positive-boundary
Wilson analysis operator itself is nonzero. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_ne_zero_of_exists_factorized_inner_self_pos
    {H : ℕ}
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hpos : ∃ f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2),
      0 < inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
          beta hbeta f)
        f) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
        beta hbeta ≠ 0 := by
  obtain ⟨f, hf⟩ := hpos
  have hAf :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_apply_ne_zero_of_factorized_inner_self_pos
      beta hbeta f hf
  intro hzero
  apply hAf
  simpa [hzero]

/-- A uniform positive lower bound on the finite four-edge adjoint/Fock
pairings survives the full Wilson-analysis limit.  This isolates exactly the
remaining cancellation-free obligation: once a protected finite-degree sector
is eventually bounded below by a fixed `delta > 0`, the genuine actual
analysis matrix coefficient is strictly positive. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilson_analysisInner_pos_of_eventually_partialAdjoint_ge
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert)
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ᶠ degree in atTop,
      delta ≤
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
          H n beta hbeta degree f q) :
    0 < inner ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
        H n q)
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
        beta hbeta f) := by
  have hlimit :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral_tendsto_inner_analysis
      hH n beta hbeta f q
  exact lt_of_lt_of_le hdelta (ge_of_tendsto hlimit hlower)

/-- Under the same eventual protected lower bound, the genuine actual Wilson
analysis output cannot be the zero `L²` vector.  No sign is inferred from a PSD
remainder; positivity comes only from the explicit eventual lower bound and
closedness of the order under the already-proved adjoint-product limit. -/
theorem
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_ne_zero_of_eventually_partialAdjoint_ge
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert)
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ᶠ degree in atTop,
      delta ≤
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
          H n beta hbeta degree f q) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
        beta hbeta f ≠ 0 := by
  have hinner :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilson_analysisInner_pos_of_eventually_partialAdjoint_ge
      hH n beta hbeta f q delta hdelta hlower
  have hinnerNe :
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 positiveBoundaryTemporalWilsonActualAnalysisNonzeroCriterionTwoRankPositive
          beta hbeta f) ≠ 0 :=
    ne_of_gt hinner
  intro hzero
  apply hinnerNe
  rw [hzero, inner_zero_right]

end

end MathlibAnalytic
end MGAP4D