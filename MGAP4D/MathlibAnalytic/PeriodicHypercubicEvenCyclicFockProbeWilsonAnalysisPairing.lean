import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullbackL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisDualProbePairingMatrix

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFockPairingTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFockPairingCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFockPairingSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFockPairingMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFockPairingBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFockPairingSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem cyclicFockPairingTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- Send the actual positive-half cyclic Fock dual probe from #1661 through
the exact Wilson Hilbert-adjoint synthesis operator.  The result is a genuine
boundary-Haar `L²` dual vector, with no change of physical measure or abstract
replacement of the Wilson kernel. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
  periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
    H 2 cyclicFockPairingTwoRankPositive beta hbeta
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q)

/-- Exact adjoint bridge: pairing the actual open-half Fock probe with Wilson
analysis is identical to pairing its actual Wilson synthesis with the boundary
input. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_synthesisBoundaryProbe_inner
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFockPairingTwoRankPositive beta hbeta f) =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
          H beta hbeta n q)
        f := by
  symm
  exact periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner
    H 2 cyclicFockPairingTwoRankPositive beta hbeta
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q) f

/-- The cyclic Fock probe paired with the `j`-th actual primary-plaquette
analysis image is exactly the boundary-Haar coefficient of the synthesized
Fock probe against the corresponding theorem-generated initial mode. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_primaryPlaquetteAnalysisImage
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (j : Fin (k + 1)) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          H beta hbeta k j) =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
          H beta hbeta n q)
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
          H k j) := by
  unfold periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_synthesisBoundaryProbe_inner
      H beta hbeta n q
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode H k j)

/-- A row of the #1645 rectangular pairing matrix built from a cyclic Fock
probe is therefore an exact boundary-Haar synthesis pairing row.  This is the
operator-level interface needed for the next density-transport step from the
nonzero interacting boundary moment of #1655. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_cyclicFockProbe_row
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
        H n q) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        H beta hbeta k probe i j =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionCyclicFockSynthesisBoundaryProbe
          H beta hbeta n q)
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
          H k j) := by
  rw [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_apply,
    hi]
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_primaryPlaquetteAnalysisImage
      H beta hbeta k n q j

end

end MathlibAnalytic
end MGAP4D
