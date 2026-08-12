import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveWeightedIntegralLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeDualProbeAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullbackL2

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace Topology

noncomputable section

local instance cyclicFourEdgeCyclicProbeIntegralTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeCyclicProbeIntegralCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeCyclicProbeIntegralSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeCyclicProbeIntegralMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeCyclicProbeIntegralBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeCyclicProbeIntegralSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual scalar cyclic degree probe is Haar integrable.  This is the
finite-measure `L² → L¹` consequence of the already constructed `MemLp 2`
probe; no additional boundedness or transport hypothesis is introduced. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_integrable
    (H n : ℕ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Integrable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  letI : IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
    dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_memLp
      H n q).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- Fixed-boundary finite four-edge Wilson Fock integral weighted by the actual
cyclic degree-`n` scalar probe. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfDegreeDualProbeIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral
    H beta hbeta degree b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)

/-- Fixed-boundary actual completed-positive Gram integral weighted by the
same cyclic degree-`n` scalar probe. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfDegreeDualProbeIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfWeightedIntegral
    H beta hbeta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)

/-- The complete rectangular four-edge Wilson Taylor/Fock approximation
converges after open-half Haar integration against the actual cyclic degree
probe. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfDegreeDualProbeIntegral_tendsto
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfDegreeDualProbeIntegral
          H n beta hbeta degree b q)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfDegreeDualProbeIntegral
          H n beta hbeta b q)) := by
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral_tendsto
      hH beta hbeta b
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_integrable
        H n q)

/-- The same finite integral written directly with the genuine four-edge
Hilbert-adjoint pullback pairing. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree b x *
      inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
          H n).feature x)
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- The actual completed-positive Gram integral written with the same genuine
four-edge adjoint pairing. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfAdjointProbeIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) : ℝ :=
  ∫ x,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 (by norm_num) beta hbeta b x *
      inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
          H n).feature x)
    ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)

/-- Pointwise cyclic-probe/adjoint identity transported through the finite
partial open-half Haar integral. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral_eq_degreeDualProbeIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral
        H n beta hbeta degree b q =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfDegreeDualProbeIntegral
        H n beta hbeta degree b q := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfDegreeDualProbeIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfWeightedIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree b x *
        inner ℝ
          (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
          ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
            H n).feature x) =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree b x *
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
          H n q x
    rw [specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_temporalCompanionOpenHalf_feature_eq_probe]

/-- Pointwise cyclic-probe/adjoint identity transported through the actual
completed-positive open-half Haar integral. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfAdjointProbeIntegral_eq_degreeDualProbeIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfAdjointProbeIntegral
        H n beta hbeta b q =
      periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfDegreeDualProbeIntegral
        H n beta hbeta b q := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfAdjointProbeIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfDegreeDualProbeIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfWeightedIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 (by norm_num) beta hbeta b x *
        inner ℝ
          (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
          ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
            H n).feature x) =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 (by norm_num) beta hbeta b x *
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
          H n q x
    rw [specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_temporalCompanionOpenHalf_feature_eq_probe]

/-- Fixed-boundary Wilson Taylor convergence in the exact four-edge adjoint
pairing form required by the actual Fubini integrand. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral_tendsto
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral
          H n beta hbeta degree b q)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfAdjointProbeIntegral
          H n beta hbeta b q)) := by
  have h :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfDegreeDualProbeIntegral_tendsto
      hH n beta hbeta b q
  simpa only [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialOpenHalfAdjointProbeIntegral_eq_degreeDualProbeIntegral,
    periodicHypercubicEvenBoundaryCompletedPositiveGramOpenHalfAdjointProbeIntegral_eq_degreeDualProbeIntegral]
    using h

end

end MathlibAnalytic
end MGAP4D
