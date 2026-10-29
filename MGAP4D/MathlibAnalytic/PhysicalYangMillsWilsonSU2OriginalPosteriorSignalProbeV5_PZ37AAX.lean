import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSingleLinkUniformRayleighCriterionV5_PZ37AAW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAX — genuine posterior signal probe toward a uniform one-link witness

AAW reduces the uniform physical centered Wilson Rayleigh floor to a
one-link response of order 1 / |original spatial links|. Its input is
an INTEGRATED, source-normalized response. This layer opens the unchanged
integral and isolates a strictly more local quantitative certificate.

For one actual link e, the authentic pointwise signal is
  (GI original centered physical two-Wilson-posterior expectation gap)^2
  / (FX original strictly positive density-contrast Haar-L2 variance).
The original link response is EXACTLY its boundary-pair-Haar integral.

If an integrable real probe w has pair-Haar mean >= rho and the genuine
pointwise signal dominates (kappa * C_H / |Links_H|) * w, then the
actual source-normalized response at that link is >= 4*rho*kappa/|Links_H|.
Here C_H is AAJ's original Haar covariance used ONLY to normalize the
unchanged centered physical Gauss-law source, not a replacement posterior.

For a volume family, a common rho>0 and kappa>0 with one such actual
link/probe per H therefore imply the positive physical Rayleigh floor
4*rho*kappa/3, via AAW's unconditional spatial translation theorem.
The pointwise lower bound and common probe mass are EXPLICIT, UNSOLVED
original-Wilson analytic obligations; this file does not assert them.
In particular it does not prove a uniform one-link witness unconditionally,
volume-uniform coercivity, a common fine interval, E/F, H1-H4, or a
continuum Yang--Mills mass gap.

Append-only, tighten-only; genuine SU(2) Wilson, two posterior laws,
pair-Haar measure, centered Gauss-law physical source and FX denominator
are preserved. No sorry/admit/axioms/native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAX_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAX_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAX_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAX_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAX_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAX_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- EXACT original positive-Wilson-β two-interacting-posterior signal
on one genuine spatial link and one original boundary-pair-Haar context. -/
noncomputable def p4Q2PZ37AAX_originalCenteredPosteriorSignal
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 /
  p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    H b hb.le z.2 e

/-- Genuine signal positivity uses the actual FX Wilson-posterior
variance, not a surrogate or an arbitrary positive denominator. -/
theorem p4Q2PZ37AAX_originalCenteredPosteriorSignal_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 ≤ p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z := by
  unfold p4Q2PZ37AAX_originalCenteredPosteriorSignal
  exact div_nonneg (sq_nonneg _)
    (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H b hb z.2 e).le

/-- GL/GJ already establish integrability of this SAME true Wilson
signal on the complete original pair-Haar boundary space. -/
theorem p4Q2PZ37AAX_originalCenteredPosteriorSignal_integrable
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Integrable
      (fun z => p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  simpa only [p4Q2PZ37AAX_originalCenteredPosteriorSignal] using
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
      H b hb (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e

/-- Opening AAK's actual response changes neither the two original
posterior laws nor the true boundary pair-Haar integral. -/
theorem p4Q2PZ37AAX_originalLinkResponse_eq_signal_integral
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e =
      ∫ z,
        p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 := by
  rfl

/-- A local pointwise two-Wilson-posterior signal estimate against an
integrable probe yields a quantitative ORIGINAL raw posterior response.
Neither the probe's positive mean nor the pointwise domination is
claimed here without an independent Wilson analytic estimate. -/
theorem p4Q2PZ37AAX_originalProbe_lower_rawResponse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ)
    (hw : Integrable w
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2))
    (rho kappa : ℝ) (hk : 0 ≤ kappa)
    (hMean : rho ≤ ∫ z, w z
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    (hPoint : ∀ z,
      (kappa * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H /
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) * w z ≤
        p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z) :
    rho * (kappa * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H /
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) ≤
        p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  let C : ℝ := p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let a : ℝ := kappa * C / L
  have hC : 0 < C := p4Q2PZ37AAJ_originalHaarCovariance_pos H
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have ha : 0 ≤ a :=
    div_nonneg (mul_nonneg hk hC.le) hL.le
  have hMono :
      (∫ z, a * w z ∂μ) ≤
      (∫ z, p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z ∂μ) := by
    apply integral_mono (hw.const_mul a)
      (p4Q2PZ37AAX_originalCenteredPosteriorSignal_integrable H b hb e)
    intro z
    exact hPoint z
  change rho * a ≤
    p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e
  calc
    rho * a ≤ (∫ z, w z ∂μ) * a :=
      mul_le_mul_of_nonneg_right hMean ha
    _ = ∫ z, a * w z ∂μ := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ z, p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z ∂μ :=
      hMono
    _ = p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e :=
      (p4Q2PZ37AAX_originalLinkResponse_eq_signal_integral H b hb e).symm

/-- The same genuinely local pointwise posterior probe supplies an
AAW-compatible normalized one-link witness with explicit 4-factor. -/
theorem p4Q2PZ37AAX_originalProbe_lower_normalizedResponse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (w : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ)
    (hw : Integrable w
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2))
    (rho kappa : ℝ) (hk : 0 ≤ kappa)
    (hMean : rho ≤ ∫ z, w z
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    (hPoint : ∀ z,
      (kappa * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H /
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) * w z ≤
        p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z) :
    (4 * rho * kappa) /
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e := by
  let C : ℝ := p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let J : ℝ := p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e
  have hC : 0 < C := p4Q2PZ37AAJ_originalHaarCovariance_pos H
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hRaw : rho * ((kappa * C) / L) ≤ J :=
    p4Q2PZ37AAX_originalProbe_lower_rawResponse
      H b hb e w hw rho kappa hk hMean hPoint
  have hRatio : (rho * kappa * C) / L ≤ J := by
    convert hRaw using 1 <;> ring
  have hScaled : rho * kappa * C ≤ J * L :=
    (div_le_iff₀ hL).mp hRatio
  change (4 * rho * kappa) / L ≤ (4 * J) / C
  apply (div_le_div_iff₀ hL hC).mpr
  nlinarith only [hScaled]

/-- A VOLUME-UNIFORM positive physical Rayleigh floor follows from
a new explicit analytic task: for every original finite Wilson volume,
find ONE actual link and an original boundary-pair-Haar integrable probe
of a COMMON positive mean rho, whose genuine pointwise two-interacting-
posterior gap-square / FX variance signal dominates a COMMON positive
kappa times the ORIGINAL physical source covariance / link count.

The existence of such probes and pointwise estimates is NOT proved.
The conclusion is conditional, not an unconditional mass-gap result. -/
theorem p4Q2PZ37AAX_uniformRayleigh_of_truePosteriorProbes
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (rho kappa : ℝ) (hrho : 0 < rho) (hk : 0 < kappa)
    (w : ∀ H : ℕ,
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ)
    (hw : ∀ H, Integrable (w H)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2))
    (hMean : ∀ H, rho ≤ ∫ z, (w H) z
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    (hLocal : ∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ∀ z,
        (kappa * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H /
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)) *
            (w H) z ≤
          p4Q2PZ37AAX_originalCenteredPosteriorSignal H (b H) (hb H) e z) :
    0 < (4 * rho * kappa) / 3 ∧
      ∀ H, (4 * rho * kappa) / 3 ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  have hc : 0 < (4 * rho * kappa) / 3 := by positivity
  refine ⟨hc, ?_⟩
  intro H
  obtain ⟨e, hPoint⟩ := hLocal H
  have hWitness :
      (4 * rho * kappa) /
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
          p4Q2PZ37AAK_originalNormalizedLinkResponse H (b H) (hb H) e :=
    p4Q2PZ37AAX_originalProbe_lower_normalizedResponse
      H (b H) (hb H) e (w H) (hw H) rho kappa hk.le (hMean H) hPoint
  apply p4Q2PZ37AAW_originalRayleighFloor_of_tripleScaledSingleLink
    H (b H) (hb H) ((4 * rho * kappa) / 3)
  refine ⟨e, ?_⟩
  convert hWitness using 1
  ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX_originalCenteredPosteriorSignal_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX_originalCenteredPosteriorSignal_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX_originalLinkResponse_eq_signal_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX_originalProbe_lower_rawResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX_originalProbe_lower_normalizedResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX_uniformRayleigh_of_truePosteriorProbes