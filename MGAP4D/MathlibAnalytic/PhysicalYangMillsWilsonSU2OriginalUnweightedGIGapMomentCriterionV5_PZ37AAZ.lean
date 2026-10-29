import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorPositiveEventCriterionV5_PZ37AAY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAZ — true Wilson unweighted GI-gap moment versus raw posterior response

AAY reduced the ORIGINAL positive physical centered Wilson Rayleigh floor to
quantitative signed Gauss-law expectation-gap separation on a positive
original outer boundary pair-Haar event, with the ACTUAL FX variance.

This module isolates a different non-circular analytic target: the
UNWEIGHTED pair-Haar second moment of the ORIGINAL signed expectation gap,
without dividing by FX, using the identical authentic Gauss-law physical
source and two interacting conditional Wilson laws.

For one original spatial link e let
  D(z) = original GI two-interacting-posterior expectation gap on V_H,
  Q(z) = actual strictly positive FX posterior density-contrast Haar L2,
  J_e  = original complete-pair-Haar integral of D(z)^2 / Q(z).
If the actual Q(z) <= q for all original pair-boundary contexts and the
genuine D^2 is integrable, then

  integral_pairHaar D^2 <= q * J_e.

Thus a positive UNWEIGHTED squared expectation-gap moment >= m and a
positive volume-uniform true FX upper bound q would suffice for
  R_H(V_H) >= m / (18*q),
using AAX2's exact original plaquette/link count and one-link reduction.

The FX upper bound is deliberately an EXPLICIT assumption in the new
results. An older JL volume-independent upper theorem has five inherited
legacy finite-incidence native_decide axioms in its proof, hence is NOT
imported as an authority into these standard-axiom-only certificates.
Neither the uniform unweighted gap moment nor its required integrability
and uniform variance bound is asserted here without proof.

Independently, from AAK's already proved fixed-volume strict positivity
of a TRUE original raw posterior response, we derive a genuinely
non-a.e.-zero centered physical GI expectation gap on some actual
spatial link in the ORIGINAL pair-Haar boundary measure at every H,b>0.
This is unconditional but its positive-measure detection strength may
depend on H,b.

All original Wilson SU(2) physical kernel, canonical Perron vacuum,
Gauss-law source, pair-Haar, both interacting one-link conditional
posterior laws and FX denominator are UNCHANGED. Append-only,
tighten-only, no new axioms, sorry, admit, native_decide,
coercivity, common fine interval, E/F, H1-H4 or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAZ_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAZ_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAZ_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAZ_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAZ_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The exact UNWEIGHTED, full original boundary-pair-Haar squared
two-genuine-Wilson-posterior GI expectation-gap moment on the SAME
original centered Gauss-law physical source; no surrogate integral. -/
noncomputable def p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z,
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- The TRUE original squared gap is controlled pointwise by the
original GI/FX normalized posterior signal and any legitimate upper
bound on the SAME actual FX density-contrast variance. The exact
identity D^2 = (D^2/Q)*Q is used with Q>0 already proved by FX. -/
theorem p4Q2PZ37AAZ_originalGapSquare_le_FXCap_mul_trueSignal
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (q : ℝ)
    (hQcap :
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤ q) :
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 ≤
      q * p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z := by
  let D : ℝ :=
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let Q : ℝ :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b hb.le z.2 e
  let S : ℝ := p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z
  have hQpos : 0 < Q :=
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      H b hb z.2 e
  have hSnonneg : 0 ≤ S :=
    p4Q2PZ37AAX_originalCenteredPosteriorSignal_nonneg H b hb e z
  have hEq : S * Q = D^2 := by
    change (D^2 / Q) * Q = D^2
    exact div_mul_cancel₀ (D^2) hQpos.ne'
  change D^2 ≤ q * S
  calc
    D^2 = S * Q := hEq.symm
    _ ≤ S * q := mul_le_mul_of_nonneg_left hQcap hSnonneg
    _ = q * S := mul_comm _ _

/-- If the full genuine Wilson unweighted squared GI gap is integrable
and original FX variance is actually bounded by q pointwise, its
original pair-Haar moment is at most q times the SAME AAK true raw
two-interacting-posterior response J_e. This is not a reference Haar
conditional posterior, nor a source-frame hypothesis. -/
theorem p4Q2PZ37AAZ_originalGapMoment_le_FXCap_mul_rawResponse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (q : ℝ)
    (hQcap : ∀ z,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤ q)
    (hGapInt : Integrable
      (fun z =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)) :
    p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e ≤
      q * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let S := p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e
  have hSignalInt : Integrable S μ :=
    p4Q2PZ37AAX_originalCenteredPosteriorSignal_integrable H b hb e
  have hMono :
      (∫ z,
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 ∂μ) ≤
      ∫ z, q * S z ∂μ := by
    apply integral_mono hGapInt (hSignalInt.const_mul q)
    intro z
    exact p4Q2PZ37AAZ_originalGapSquare_le_FXCap_mul_trueSignal
      H b hb e z q (hQcap z)
  change
    (∫ z,
      (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 ∂μ) ≤
    q * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e
  calc
    (∫ z,
      (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 ∂μ) ≤
        ∫ z, q * S z ∂μ := hMono
    _ = q * (∫ z, S z ∂μ) := by rw [integral_const_mul]
    _ = q * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
      rw [← p4Q2PZ37AAX_originalLinkResponse_eq_signal_integral H b hb e]

/-- A strictly positive true FX variance upper q and positive genuine
UNWEIGHTED original GI gap-square moment m yield a lower bound on
the true raw posterior response; there is NO Rayleigh input. -/
theorem p4Q2PZ37AAZ_originalRawResponse_ge_of_gapMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (m q : ℝ) (hq : 0 < q)
    (hQcap : ∀ z,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤ q)
    (hGapInt : Integrable
      (fun z =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2))
    (hMoment : m ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e) :
    m / q ≤ p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  have hBound :=
    p4Q2PZ37AAZ_originalGapMoment_le_FXCap_mul_rawResponse
      H b hb e q hQcap hGapInt
  exact (div_le_iff₀ hq).mpr (by
    simpa [mul_comm] using hMoment.trans hBound)

/-- All finite volumes, truly interacting positive Wilson couplings,
one actual link and a common positive UNWEIGHTED GI gap-square moment,
plus an independently controlled original FX variance, suffice for an
explicit volume-uniform centered physical fine-zero Rayleigh floor.
Neither analytic uniform hypothesis is claimed unconditionally. -/
theorem p4Q2PZ37AAZ_allVolumes_Rayleigh_of_trueUnweightedGIMoments
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (m q : ℝ) (hm : 0 < m) (hq : 0 < q)
    (e : ∀ H, PeriodicHypercubicEvenSpatialSliceLink H)
    (hQcap : ∀ H, ∀ z,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H (b H) (hb H).le z.2 (e H) ≤ q)
    (hGapInt : ∀ H, Integrable
      (fun z =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H (b H) (hb H).le
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) (e H) z)^2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2))
    (hMoment : ∀ H,
      m ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
        H (b H) (hb H) (e H)) :
    0 < (m / q) / 18 ∧
      ∀ H, (m / q) / 18 ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  apply p4Q2PZ37AAX2_allVolumes_uniformRayleigh_of_rawSingleLink
    b hb (m / q) (div_pos hm hq)
  intro H
  refine ⟨e H, ?_⟩
  exact p4Q2PZ37AAZ_originalRawResponse_ge_of_gapMoment
    H (b H) (hb H) (e H) m q hq
    (hQcap H) (hGapInt H) (hMoment H)

/-- Unconditionally, at EVERY fixed finite Wilson H,b>0, SOME ORIGINAL
spatial link detects the unchanged centered physical Gauss-law source
on a non-a.e.-zero set of the ACTUAL outer boundary pair-Haar law.
This is substantially stronger than a pointwise Haar-null witness,
but gives no volume-uniform positive measure or signal amplitude. -/
theorem p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ¬ (∀ᵐ z
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z = 0) := by
  obtain ⟨e, he⟩ :=
    p4Q2PZ37AAK_exists_originalLink_positiveResponse H b hb
  refine ⟨e, ?_⟩
  intro hZero
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  have hSignalAE :
      (fun z => p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z) =ᵐ[μ]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hZero] with z hz
    simp [p4Q2PZ37AAX_originalCenteredPosteriorSignal, hz]
  have hJZero : p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e = 0 := by
    rw [p4Q2PZ37AAX_originalLinkResponse_eq_signal_integral]
    calc
      (∫ z, p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e z ∂μ) =
        ∫ _z, (0 : ℝ) ∂μ := integral_congr_ae hSignalAE
      _ = 0 := by simp
  exact (ne_of_gt he) hJZero

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ_originalGapSquare_le_FXCap_mul_trueSignal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ_originalGapMoment_le_FXCap_mul_rawResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ_originalRawResponse_ge_of_gapMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ_allVolumes_Rayleigh_of_trueUnweightedGIMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero