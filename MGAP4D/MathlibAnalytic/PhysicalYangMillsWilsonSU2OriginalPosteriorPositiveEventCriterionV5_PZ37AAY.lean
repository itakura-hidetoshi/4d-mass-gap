import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorRawMassUniformV5_PZ37AAX2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAY — original Wilson posterior positive-measure event witness

AAX2 reduced a volume-uniform positive centered physical Wilson Rayleigh
floor to one actual UNNORMALIZED genuine two-interacting-posterior
GI-gap-square/FX-variance link response, uniformly positive in H.

We now resolve the exact REAL local event certificate needed to get
such a raw response, without appealing to the unknown Rayleigh value:

* E is a measurable subset of the ORIGINAL boundary pair-Haar
  configuration space; 1_E is its authentic Haar indicator.
* Its original pair-Haar mass is at least rho, expressed as the
  integral of that indicator.
* On E, the absolute ORIGINAL centered Gauss-law two-conditional-Wilson-
  posterior GI expectation gap is at least delta.
* On E, the genuine strictly positive FX Haar-L2 posterior contrast
  variance is at most q.

The original unnormalized Wilson link signal is gap^2 / FX variance;
the true link integral is therefore >= rho*delta^2/q. Consequently
common positive rho, delta and q with a suitable true event and link
per volume yield the explicit fine-zero physical Rayleigh floor

    rho*delta^2 / (18*q).

This is a strictly more geometrically concrete, EVENT-SUPPORTED
posterior certificate than the general AAX test function and contains
no unknown Rayleigh term in any hypothesis. NO unconditional existence
of such a uniform event, gap, or FX upper bound is asserted.
Neither original interacting Wilson posterior is replaced by Haar;
pair-Haar is only the OUTER unchanged boundary law. The same original
physical centered Gauss-law source and actual spatial link are used.

No new axioms, sorry/admit/native_decide, overwrite, Dobrushin, common
positive fine interval, E/F, H1-H4, or 4D continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAY_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAY_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAY_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAY_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAY_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AAY_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G
local instance p4Q2PZ37AAY_spatialProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AAY_pairProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- An authentic measurable ORIGINAL boundary pair-Haar event, with
quantitative centered Gauss-law GI expectation separation and FX
posterior-contrast variance bound, yields a raw actual-link response
lower bound. No surrogate conditional, no pointwise positivity outside
the event, and no uniformity assumption is concealed. -/
theorem p4Q2PZ37AAY_originalRawLinkResponse_ge_trueEventSignal
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
    (hE : MeasurableSet E)
    (rho delta q : ℝ) (hdelta : 0 ≤ delta) (hq : 0 < q)
    (hMass : rho ≤
      ∫ z, E.indicator (fun _ => (1 : ℝ)) z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    (hGap : ∀ z ∈ E,
      delta ≤ |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z|)
    (hVar : ∀ z ∈ E,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤ q) :
    rho * (delta^2 / q) ≤
      p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let Q : Pair → ℝ := fun z =>
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b hb.le z.2 e
  let S : Pair → ℝ :=
    p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e
  let w : Pair → ℝ := E.indicator (fun _ => (1 : ℝ))
  let k : ℝ := delta^2 / q
  have hk : 0 ≤ k := div_nonneg (sq_nonneg _) hq.le
  have hSignalInt : Integrable S μ :=
    p4Q2PZ37AAX_originalCenteredPosteriorSignal_integrable H b hb e
  have hProbeInt : Integrable w μ :=
    (integrable_const (1 : ℝ)).indicator hE
  have hMean : rho ≤ ∫ z, w z ∂μ := hMass
  have hSq (z : Pair) (hz : z ∈ E) :
      delta^2 ≤ (D z)^2 := by
    have hAbs : delta ≤ |D z| := hGap z hz
    by_cases hPos : 0 ≤ D z
    · rw [abs_of_nonneg hPos] at hAbs
      have hMul : 0 ≤ (D z - delta) * (D z + delta) :=
        mul_nonneg (sub_nonneg.mpr hAbs) (add_nonneg hPos hdelta)
      nlinarith only [hMul]
    · have hNeg : D z ≤ 0 := le_of_lt (lt_of_not_ge hPos)
      rw [abs_of_nonpos hNeg] at hAbs
      have hMul : 0 ≤ (-D z - delta) * (-D z + delta) :=
        mul_nonneg (sub_nonneg.mpr hAbs)
          (add_nonneg (neg_nonneg.mpr hNeg) hdelta)
      nlinarith only [hMul]
  have hPoint (z : Pair) : k * w z ≤ S z := by
    by_cases hz : z ∈ E
    · have hQ : 0 < Q z :=
        p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
          H b hb z.2 e
      have hDiv : delta^2 / q ≤ (D z)^2 / Q z := by
        apply (div_le_div_iff₀ hq hQ).mpr
        calc
          delta^2 * Q z ≤ delta^2 * q :=
            mul_le_mul_of_nonneg_left (hVar z hz) (sq_nonneg _)
          _ ≤ (D z)^2 * q :=
            mul_le_mul_of_nonneg_right (hSq z hz) hq.le
      have hwz : w z = 1 := by simp [w, Set.indicator, hz]
      rw [hwz, mul_one]
      change delta^2 / q ≤ (D z)^2 / Q z
      exact hDiv
    · have hwz : w z = 0 := by simp [w, Set.indicator, hz]
      rw [hwz, mul_zero]
      exact p4Q2PZ37AAX_originalCenteredPosteriorSignal_nonneg H b hb e z
  have hIntegral :
      (∫ z, k * w z ∂μ) ≤ (∫ z, S z ∂μ) := by
    apply integral_mono (hProbeInt.const_mul k) hSignalInt
    intro z
    exact hPoint z
  change rho * k ≤
    p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e
  calc
    rho * k ≤ (∫ z, w z ∂μ) * k :=
      mul_le_mul_of_nonneg_right hMean hk
    _ = ∫ z, k * w z ∂μ := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ z, S z ∂μ := hIntegral
    _ = p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e :=
      (p4Q2PZ37AAX_originalLinkResponse_eq_signal_integral H b hb e).symm

/-- A common positive-measure original pair-Haar event with an authentic
uniform positive physical GI gap and FX variance upper bound at ONE
actual spatial link per volume forces an explicit all-volume original
centered physical Wilson fine-zero Rayleigh floor.

The independent event/gap/variance hypotheses are NOT proven here. -/
theorem p4Q2PZ37AAY_allVolumes_uniformRayleigh_of_trueEvents
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (rho delta q : ℝ) (hrho : 0 < rho) (hdelta : 0 < delta) (hq : 0 < q)
    (e : ∀ H, PeriodicHypercubicEvenSpatialSliceLink H)
    (E : ∀ H, Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
    (hE : ∀ H, MeasurableSet (E H))
    (hMass : ∀ H, rho ≤
      ∫ z, (E H).indicator (fun _ => (1 : ℝ)) z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
    (hGap : ∀ H, ∀ z ∈ E H,
      delta ≤ |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H (b H) (hb H).le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) (e H) z|)
    (hVar : ∀ H, ∀ z ∈ E H,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H (b H) (hb H).le z.2 (e H) ≤ q) :
    0 < (rho * (delta^2 / q)) / 18 ∧
      ∀ H, (rho * (delta^2 / q)) / 18 ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  have hEps : 0 < rho * (delta^2 / q) :=
    mul_pos hrho (div_pos (pow_pos hdelta 2) hq)
  apply p4Q2PZ37AAX2_allVolumes_uniformRayleigh_of_rawSingleLink
    b hb (rho * (delta^2 / q)) hEps
  intro H
  refine ⟨e H, ?_⟩
  exact p4Q2PZ37AAY_originalRawLinkResponse_ge_trueEventSignal
    H (b H) (hb H) (e H) (E H) (hE H)
    rho delta q hdelta.le hq (hMass H)
    (hGap H) (hVar H)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAY_originalRawLinkResponse_ge_trueEventSignal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAY_allVolumes_uniformRayleigh_of_trueEvents