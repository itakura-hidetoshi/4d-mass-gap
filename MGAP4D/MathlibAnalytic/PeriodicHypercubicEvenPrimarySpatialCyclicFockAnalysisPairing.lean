import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullbackL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFockAnalysisPairingTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFockAnalysisPairingCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFockAnalysisPairingSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFockAnalysisPairingMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFockAnalysisPairingBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFockAnalysisPairingBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance cyclicFockAnalysisPairingOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance cyclicFockAnalysisPairingSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual Wilson boundary-to-open-half analysis pairing against the
cyclic temporal-companion degree probe constructed in the preceding layer.

This theorem is deliberately carrier-level only: it identifies the #1661
open-half `L²` probe with the exact rectangular Hilbert--Schmidt pairing used
by the #1645 finite probe matrix, without yet asserting that this scalar is
nonzero. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis
    (H n : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 (by norm_num) beta hbeta f) =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H 2 (by norm_num) beta hbeta)
        f
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q) := by
  rw [real_inner_comm]
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
      H 2 (by norm_num) beta hbeta f
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
        H n q)

/-- Boundary-Haar `L²` vector obtained by applying the actual Wilson Hilbert
adjoint synthesis operator to the cyclic temporal-companion Fock probe. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeBoundarySynthesisL2
    (H n : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
  periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
    H 2 (by norm_num) beta hbeta
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q)

/-- The synthesized boundary vector has exactly the same matrix coefficients
as pairing the cyclic open-half probe against actual Wilson analysis. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeBoundarySynthesisL2_inner
    (H n : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeBoundarySynthesisL2
          H n beta hbeta q)
        f =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 (by norm_num) beta hbeta f) := by
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
        H n q)
      f

/-- Combined adjoint/Hilbert--Schmidt form of the cyclic Fock probe pairing.
The three carriers that were previously separate are now one theorem-level
identity:

`⟪A† u_q, f⟫ = ⟪u_q, A f⟫ = B_K(f,u_q)`.
-/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeBoundarySynthesisL2_inner_eq_kernelPairing
    (H n : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeBoundarySynthesisL2
          H n beta hbeta q)
        f =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H 2 (by norm_num) beta hbeta)
        f
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeBoundarySynthesisL2_inner,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis]

end

end MathlibAnalytic
end MGAP4D
