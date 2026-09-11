import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeDualProbeAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFockProbeWilsonAnalysisFubini

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFourEdgeFubiniAdjointTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeFubiniAdjointCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeFubiniAdjointSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeFubiniAdjointMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeFubiniAdjointBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeFubiniAdjointBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance cyclicFourEdgeFubiniAdjointOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance cyclicFourEdgeFubiniAdjointSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The #1662 Wilson-analysis Fubini formula with its cyclic scalar probe
replaced pointwise by the exact four-edge Hilbert-adjoint pullback pairing.

No Wilson factor is modified and no marginal transport identity is assumed.
This theorem only exposes the arbitrary-degree source carrier inside the actual
boundary/open-half Haar integral. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_iteratedIntegral_fourEdgeAdjoint
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
      ∫ b, ∫ x,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 (by norm_num) beta hbeta b x *
          (f b *
            inner ℝ
              (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
              ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
                H n).feature x))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_iteratedIntegral]
  apply integral_congr_ae
  filter_upwards with b
  apply integral_congr_ae
  filter_upwards with x
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_eq_fourEdgePowerDualPullbackInner]

end

end MathlibAnalytic
end MGAP4D
