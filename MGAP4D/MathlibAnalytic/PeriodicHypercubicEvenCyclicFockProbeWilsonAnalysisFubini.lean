import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFockProbeWilsonAnalysisPairing
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFockFubiniTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFockFubiniCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFockFubiniSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFockFubiniMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFockFubiniBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFockFubiniBoundaryHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance cyclicFockFubiniOpenHalfHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance cyclicFockFubiniSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem cyclicFockFubini_realScalar_inner_eq_mul
    (x y : ℝ) :
    inner ℝ x y = x * y := by
  change y * x = x * y
  exact mul_comm y x

/-- The rectangular Wilson `L²` kernel has the raw completed-positive feature
as its almost-everywhere representative. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_cyclicFockPairing_coeFn
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun p =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H 2 (by norm_num) beta hbeta p) =ᵐ[
      (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)]
      (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 (by norm_num) beta hbeta p.1 p.2) := by
  let hmem :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H 2 (by norm_num) beta hbeta
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2,
    periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
      hmem.coeFn_toLp

/-- The raw Wilson completed-positive feature times a boundary `L²` vector and
the actual cyclic Fock probe is integrable on boundary × open-half Haar.
This is the finite-Haar instance of Mathlib's `L² × L² → L¹` mechanism. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_weightedPair_integrable
    (H n : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 (by norm_num) beta hbeta p.1 p.2 *
          (f p.1 *
            periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
              H n q p.2))
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H 2 (by norm_num) beta hbeta
  let g :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q
  let E := realL2ExternalTensor f g
  have hinner : Integrable
      (fun p => inner ℝ (K p) (E p))
      (boundaryMeasure.prod halfMeasure) :=
    MeasureTheory.L2.integrable_inner K E
  apply hinner.congr
  filter_upwards [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_cyclicFockPairing_coeFn
      H beta hbeta,
    realL2ExternalTensor_coeFn
      (μ := boundaryMeasure) (ν := halfMeasure) f g] with p hK hE
  rw [show K p = periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 (by norm_num) beta hbeta p.1 p.2 by exact hK]
  rw [show E p = f p.1 * g p.2 by exact hE]
  exact cyclicFockFubini_realScalar_inner_eq_mul _ _

/-- Exact Fubini representative of the cyclic Fock / actual Wilson analysis
matrix coefficient.

The #1661 probe and the genuine completed-positive Wilson kernel now occur
pointwise in the same formula.  Hence the remaining model-specific calculation
is the inner open-half Haar integral; no Hilbert quotient, adjoint-synthesis,
or product-measure transport remains hidden. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_iteratedIntegral
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
            periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
              H n q x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H 2 (by norm_num) beta hbeta
  let g :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q
  let raw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 (by norm_num) beta hbeta p.1 p.2 * (f p.1 * g p.2)
  have hraw : Integrable raw (boundaryMeasure.prod halfMeasure) := by
    simpa [raw, boundaryMeasure, halfMeasure, g] using
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_weightedPair_integrable
        H n beta hbeta q f
  calc
    inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 (by norm_num) beta hbeta f) =
      realL2HilbertSchmidtKernelPairing K f g := by
        rw [real_inner_comm]
        simpa [K, g] using
          periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
            H 2 (by norm_num) beta hbeta f g
    _ = ∫ p, raw p ∂(boundaryMeasure.prod halfMeasure) := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_cyclicFockPairing_coeFn
          H beta hbeta,
        realL2ExternalTensor_coeFn
          (μ := boundaryMeasure) (ν := halfMeasure) f g] with p hK hfg
      rw [show K p = periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 (by norm_num) beta hbeta p.1 p.2 by exact hK]
      rw [show realL2ExternalTensor f g p = f p.1 * g p.2 by exact hfg]
      rw [cyclicFockFubini_realScalar_inner_eq_mul]
    _ = ∫ b, ∫ x, raw (b, x) ∂halfMeasure ∂boundaryMeasure := by
      exact MeasureTheory.integral_prod raw hraw
    _ = ∫ b, ∫ x,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 (by norm_num) beta hbeta b x *
          (f b *
            periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
              H n q x)
        ∂halfMeasure ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards with b
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_coeFn
          H n q] with x hx
      simp only [raw]
      rw [show g x =
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
            H n q x by exact hx]

end

end MathlibAnalytic
end MGAP4D
