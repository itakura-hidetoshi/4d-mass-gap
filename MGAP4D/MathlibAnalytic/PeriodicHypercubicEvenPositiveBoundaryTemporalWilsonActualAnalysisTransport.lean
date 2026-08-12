import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonAnalysisProtectedWitnessLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Inverse

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private theorem positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveBoundaryTemporalWilsonActualAnalysisTransportTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveBoundaryTemporalWilsonActualAnalysisTransportCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisTransportSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveBoundaryTemporalWilsonActualAnalysisTransportMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisTransportBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveBoundaryTemporalWilsonActualAnalysisTransportSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The centered normalized-trace polynomial as an actual interacting-boundary
`L²` vector.  This packages exactly the vector used by the strict Fock moment
theorems, without changing its measure or coefficients. -/
noncomputable def
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    PeriodicHypercubicEvenBoundaryMarginalL2 H 2
      positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta :=
  ∑ j : Fin (k + 1), c j •
    ContinuousMap.toLp (E := ℝ) 2
      (periodicHypercubicEvenBoundaryMarginalMeasure H 2
        positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta) ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
        (j : ℕ))

/-- The constant boundary vacuum vector on interacting-boundary `L²`. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalVacuumL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryMarginalL2 H 2
      positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta :=
  ContinuousMap.toLp (E := ℝ) 2
    (periodicHypercubicEvenBoundaryMarginalMeasure H 2
      positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta) ℝ
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
      (0 : ℕ))

/-- Exact square-root-density transport of the interacting normalized-trace
polynomial into the actual boundary Haar `L²` carrier of the Wilson analysis
operator. -/
noncomputable def periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H 2 :=
  periodicHypercubicEvenBoundaryMarginalToHaarL2
    H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
      H beta hbeta k c)

/-- Exact square-root-density transport of the interacting boundary vacuum into
boundary Haar `L²`.  It is the Haar-side vacuum against which transported
centeredness is measured. -/
noncomputable def periodicHypercubicEvenBoundaryVacuumHaarL2
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H 2 :=
  periodicHypercubicEvenBoundaryMarginalToHaarL2
    H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)

/-- The transported normalized-trace polynomial returns exactly to the original
interacting-marginal `L²` vector under reciprocal-vacuum transport. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_toMarginal
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2
        H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta k c) =
      periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
        H beta hbeta k c := by
  unfold periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
  exact periodicHypercubicEvenBoundaryHaarToMarginalL2_marginalToHaar
    H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
      H beta hbeta k c)

/-- The transported boundary vacuum returns exactly to the interacting constant
vacuum vector. -/
theorem periodicHypercubicEvenBoundaryVacuumHaarL2_toMarginal
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2
        H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
        (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta) =
      periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta := by
  unfold periodicHypercubicEvenBoundaryVacuumHaarL2
  exact periodicHypercubicEvenBoundaryHaarToMarginalL2_marginalToHaar
    H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)

/-- Square-root-density transport preserves the polynomial `L²` norm exactly. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_norm
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    ‖periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        H beta hbeta k c‖ =
      ‖periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
        H beta hbeta k c‖ := by
  unfold periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
  exact periodicHypercubicEvenBoundaryMarginalToHaarL2_norm
    H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
      H beta hbeta k c)

/-- Centeredness is transported exactly from the interacting boundary marginal
to the actual boundary Haar carrier.  No density-defect or approximation
hypothesis occurs: this is just the inverse/forward isometry identity. -/
theorem periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_centered
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          H beta hbeta k c) = 0) :
    inner ℝ
      (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta)
      (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
        H beta hbeta k c) = 0 := by
  have hinner := periodicHypercubicEvenBoundaryHaarToMarginalL2_inner
    H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
    (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta)
    (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
      H beta hbeta k c)
  calc
    inner ℝ
        (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta)
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta k c) =
      inner ℝ
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
          (periodicHypercubicEvenBoundaryVacuumHaarL2 H beta hbeta))
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta
          (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
            H beta hbeta k c)) := hinner.symm
    _ = inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2 H beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          H beta hbeta k c) := by
      rw [periodicHypercubicEvenBoundaryVacuumHaarL2_toMarginal,
        periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_toMarginal]
    _ = 0 := hzero

/-- The protected positive-degree witness, its exact interacting-to-Haar
transport, and the genuine full-independent four-edge Wilson analysis limit are
now one theorem on the actual analysis carrier.

The conclusion deliberately keeps the final matrix coefficient as a limit.  A
nonzero limit still requires a cancellation-free `A†A`/orthogonality bridge;
PSD of a rectangular remainder alone does not justify a sign claim. -/
theorem
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_actualBoundaryHaarTransport_protectedGram_and_analysisLimit
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
            positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta.le)) ≠ 0 ∧
        0 < ((Real.exp (-beta)) ^
          (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeCoefficient beta (i : ℕ)) *
          (∫ b₁, ∫ b₂, inner ℝ
            (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
              H k c (i : ℕ) b₁)
            (periodicHypercubicEvenBoundaryMarginalWeightedFourEdgeDegreeFeature
              H k c (i : ℕ) b₂)
            ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
              positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta.le)
            ∂(periodicHypercubicEvenBoundaryMarginalMeasure H 2
              positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta.le)) ∧
        periodicHypercubicEvenBoundaryHaarToMarginalL2
            H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta.le
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
              H 2 positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive
              beta hbeta.le
              (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
                H beta hbeta.le k c)))) := by
  have hzero' :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure H 2
            positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure H 2
              positiveBoundaryTemporalWilsonActualAnalysisTransportTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0 := by
    simpa [periodicHypercubicEvenBoundaryMarginalVacuumL2,
      periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2] using hzero
  rcases
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_protectedPositiveBoundaryWilsonSelectedGram_strict
      H beta hbeta k c hc hzero' with
    ⟨i, hi, q, hq, hstrict⟩
  refine ⟨i, hi, q, hq, hstrict, ?_, ?_, ?_, ?_⟩
  · exact periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_toMarginal
      H beta hbeta.le k c
  · exact periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_norm
      H beta hbeta.le k c
  · exact periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2_centered
      H beta hbeta.le k c hzero
  · exact
      (periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeGram_pos_and_fourEdgeWilsonAnalysisLimit_of_cyclicDualProbe
        hH beta hbeta k (i : ℕ) c q hq).2
        (periodicHypercubicEvenBoundaryNormalizedTracePolynomialHaarL2
          H beta hbeta.le k c)

end

end MathlibAnalytic
end MGAP4D
