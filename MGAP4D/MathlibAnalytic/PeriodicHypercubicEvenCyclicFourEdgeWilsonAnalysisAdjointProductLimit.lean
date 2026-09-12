import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonAnalysisProductLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

private theorem cyclicFourEdgeWilsonAnalysisAdjointProductLimitTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeWilsonAnalysisAdjointProductLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonAnalysisAdjointProductLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonAnalysisAdjointProductLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonAnalysisAdjointProductLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonAnalysisAdjointProductLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonAnalysisAdjointProductLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The finite full rectangular four-edge Wilson Taylor/Fock product pairing,
written with the genuine degree-`n` four-edge Hilbert-adjoint pullback rather
than the scalar cyclic probe representative. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) : ℝ :=
  ∫ p,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree p.1 p.2 *
      (f p.1 *
        inner ℝ
          (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
          ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
            H n).feature p.2))
    ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2)

/-- On product Haar, the exact four-edge adjoint integrand is almost
everywhere the same as the canonical cyclic `L²` probe integrand.  The only
a.e. step is replacement of the chosen `L²` representative; the adjoint/probe
identity itself is pointwise exact. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral_eq_cyclicProbe
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
        H n beta hbeta degree f q =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral
        H n beta hbeta degree f q := by
  have hProbeProduct :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q p.2) =ᵐ[
            periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2]
        fun p =>
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
            H n q p.2 := by
    simpa [periodicHypercubicEvenBoundaryOpenHalfHaarMeasure, Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd
        (μ := periodicHypercubicEvenBoundaryHaarMeasure H 2)
        (ν := periodicHypercubicEvenOpenHalfHaarMeasure H 2)).ae_eq
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_coeFn
          H n q)
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral
  apply integral_congr_ae
  filter_upwards [hProbeProduct] with p hp
  have hadj :
      inner ℝ
          (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
          ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
            H n).feature p.2) =
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
          H n q p.2 := by
    exact
      specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_temporalCompanionOpenHalf_feature_eq_probe
        H n q p.2
  rw [hadj, ← hp]

/-- The complete independent four-edge Wilson Taylor/Fock approximation,
expressed through the genuine four-edge Hilbert adjoint, converges directly to
the actual finite-Wilson analysis matrix coefficient.  In particular, no
replacement by an equal-degree diagonal Taylor sector and no transport-defect
vanishing assumption occurs in this limit. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral_tendsto_inner_analysis
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral
          H n beta hbeta degree f q)
      atTop
      (𝓝
        (inner ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
            H n q)
          (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H 2 cyclicFourEdgeWilsonAnalysisAdjointProductLimitTwoRankPositive
            beta hbeta f))) := by
  have h :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral_tendsto_inner_analysis
      hH n beta hbeta f q
  simpa only [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAdjointProbeProductIntegral_eq_cyclicProbe]
    using h

end

end MathlibAnalytic
end MGAP4D
