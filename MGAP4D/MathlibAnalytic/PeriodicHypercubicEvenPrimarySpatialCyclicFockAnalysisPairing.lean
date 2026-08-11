import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullbackL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator
import Mathlib.MeasureTheory.Integral.Prod

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

private theorem cyclicFockAnalysisPairing_realScalar_inner_eq_mul
    (x y : ℝ) :
    inner ℝ x y = x * y := by
  change y * x = x * y
  exact mul_comm y x

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

/-- The rectangular Wilson kernel has the raw completed-positive Gram feature
as its almost-everywhere representative.  This is kept in the present
finite-Wilson layer so the cyclic Fock pairing does not depend on the heavier
physical boundary-moment module. -/
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
the actual cyclic Fock probe is integrable on boundary × open-half Haar.  This
is precisely Mathlib's `L² × L² → L¹` Cauchy--Schwarz mechanism. -/
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
  exact cyclicFockAnalysisPairing_realScalar_inner_eq_mul _ _

/-- Exact Fubini representative of the cyclic Fock / actual Wilson analysis
matrix coefficient.

The #1661 probe and the genuine completed-positive Wilson kernel now appear
pointwise in the same formula.  Consequently the only remaining model-specific
calculation is the inner open-half Haar integral; no Hilbert quotient,
analysis/synthesis, or product-measure transport remains hidden. -/
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
        simpa [K, g] using
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis
            H n beta hbeta q f
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
      rw [cyclicFockAnalysisPairing_realScalar_inner_eq_mul]
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
