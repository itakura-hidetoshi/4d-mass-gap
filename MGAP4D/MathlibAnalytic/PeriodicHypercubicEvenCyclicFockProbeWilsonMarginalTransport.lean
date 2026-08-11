import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFockProbeWilsonAnalysisPairing
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockBoundedContinuousProbe
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Isometry

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFockMarginalTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFockMarginalCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFockMarginalSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFockMarginalMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFockMarginalBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFockMarginalSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem cyclicFockMarginalTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- The #1655/#1656 degree-feature dual vector as an actual interacting
boundary-marginal `L²` vector.  Its representative is exactly the bounded
continuous scalar dual observable `b ↦ ⟪q, Φ_i(b)⟫`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Lp ℝ 2
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFockMarginalTwoRankPositive beta hbeta) :=
  ContinuousMap.toLp
    (E := ℝ) 2
    (periodicHypercubicEvenBoundaryMarginalMeasure
      H 2 cyclicFockMarginalTwoRankPositive beta hbeta) ℝ
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeBoundedContinuous
      H n q).toContinuousMap

/-- Its pairing with the normalized-trace polynomial is exactly the scalar
boundary integral used in #1656. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2_inner_polynomial
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k n : ℕ) (c : Fin (k + 1) → ℝ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2
          H beta hbeta n q)
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 cyclicFockMarginalTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c)) =
      ∫ b,
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeBoundedContinuous
            H n q b
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 cyclicFockMarginalTwoRankPositive beta hbeta) := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2,
    continuous_compact_oriented_real_inner_eq_mul, mul_comm] using
    (MeasureTheory.ContinuousMap.inner_toLp
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFockMarginalTwoRankPositive beta hbeta)
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeBoundedContinuous
        H n q).toContinuousMap
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c))

/-- Transport the actual Wilson-synthesized cyclic Fock probe from boundary
Haar `L²` to the interacting boundary marginal by the already-proved reciprocal
vacuum isometry. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Lp ℝ 2
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFockMarginalTwoRankPositive beta hbeta) :=
  periodicHypercubicEvenBoundaryHaarToMarginalL2
    H 2 cyclicFockMarginalTwoRankPositive beta hbeta
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
      H beta hbeta n q)

/-- The density transport preserves exactly the synthesis pairing. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe_inner
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe
          H beta hbeta n q)
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H 2 cyclicFockMarginalTwoRankPositive beta hbeta f) =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
          H beta hbeta n q)
        f := by
  exact periodicHypercubicEvenBoundaryHaarToMarginalL2_inner
    H 2 cyclicFockMarginalTwoRankPositive beta hbeta
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
      H beta hbeta n q) f

/-- The exact remaining model-specific transport defect.  Vanishing means the
actual Wilson adjoint synthesis of the temporal-companion Fock probe is exactly
the #1655/#1656 scalar dual observable after the canonical Haar-to-marginal
density change. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Lp ℝ 2
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 cyclicFockMarginalTwoRankPositive beta hbeta) :=
  periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe
      H beta hbeta n q -
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2
      H beta hbeta n q

/-- Defect zero is exactly the desired Wilson/Fock marginal transport identity. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect_eq_zero_iff
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect
        H beta hbeta n q = 0 ↔
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe
          H beta hbeta n q =
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2
          H beta hbeta n q := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr

/-- Once the single marginal transport defect vanishes, every actual Wilson
analysis pairing with the temporal-companion Fock probe becomes exactly the
interacting-marginal pairing of the #1655/#1656 dual observable against the
canonical density-transported boundary input. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_marginalDualProbe_inner_of_transportDefect_eq_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (htransport :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect
        H beta hbeta n q = 0) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFockMarginalTwoRankPositive beta hbeta f) =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2
          H beta hbeta n q)
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H 2 cyclicFockMarginalTwoRankPositive beta hbeta f) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_synthesisBoundaryProbe_inner]
  rw [← periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe_inner]
  rw [(periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect_eq_zero_iff
    H beta hbeta n q).mp htransport]

/-- Corresponding #1645 pairing-matrix row reduction.  The only missing model
identity is now the explicit marginal transport defect above. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_cyclicFockProbe_row_eq_marginalDualProbe_inner_of_transportDefect_eq_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (i j : Fin (k + 1))
    (hi : probe i =
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
        H n q)
    (htransport :
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect
        H beta hbeta n q = 0) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        H beta hbeta k probe i j =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceDegreeDualProbeMarginalL2
          H beta hbeta n q)
        (periodicHypercubicEvenBoundaryHaarToMarginalL2
          H 2 cyclicFockMarginalTwoRankPositive beta hbeta
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
            H k j)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_cyclicFockProbe_row
    H beta hbeta k n q probe i j hi]
  rw [← periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisMarginalProbe_inner]
  rw [(periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockMarginalTransportDefect_eq_zero_iff
    H beta hbeta n q).mp htransport]

end

end MathlibAnalytic
end MGAP4D
