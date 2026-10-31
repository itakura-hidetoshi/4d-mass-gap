import MGAP4D.MathlibAnalytic.CompactProbabilityUpperEvent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceRegionV5_PZ37ACD
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapMomentCriterionV5_PZ37AAZ

/-!
# P4-Q2-PZ37ACE — genuine GI moment, event mass and physical Rayleigh

Discharge AAZ's integrability input using HI's actual joint continuity. The
AAZ non-a.e.-zero theorem then implies a strictly positive UNWEIGHTED GI
second moment on an actual link at every finite H and every b>0. An actual
compact supremum cap K yields the open event {z | M/2 < gap(z)^2} and the
explicit lower bound Haar(event) >= M/(2*K)>0. Neither M nor K is declared
volume-uniform; K is the norm of the SAME original continuous squared gap.

Connect ACD's covariance/variance event to the SAME true raw posterior
response and centered physical Rayleigh floor with the explicit bound
(Haar(S)*delta^2/q)/18. The original FX cap q remains an explicit independent
premise. A family theorem retains all common positive-moment/cap obligations.

Boundary: nonzero GI does NOT prove nonzero Haar energy covariance. This
module does not discharge the centered-source covariance witness, the ACC
positive covariance-margin threshold, a uniform event/moment lower bound,
all-source coercivity, a common positive-fine interval, or reconstruction.
All original sources, interacting posteriors, transfer norms and Haar laws
are unchanged. Existing files, assumptions, public roots and pins are intact.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACE_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACE_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACE_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACE_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACE_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "M" => p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "Delta" => p4Q2PZ37ACD_quantitativeCovarianceMargin
local instance p4Q2PZ37ACE_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACE_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Integrability is a proved property of the genuine original squared gap. -/
theorem p4Q2PZ37ACE_originalGapSquare_integrable
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Integrable (fun z : Cfg × Cfg => (gap b hb.le f₀ e z) ^ 2) outer :=
  ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
    H b hb.le f₀ e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Nonnegativity uses the actual full outer pair-Haar square integral. -/
theorem p4Q2PZ37ACE_originalMoment_nonneg
    (b : ℝ) (hb : 0 < b) (e : Link) : 0 ≤ M b hb e :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Every finite H,b>0 has an actual link with strictly positive unweighted
GI second moment. This does not assert energy-covariance nonvanishing. -/
theorem p4Q2PZ37ACE_exists_originalMoment_pos
    (b : ℝ) (hb : 0 < b) : ∃ e : Link, 0 < M b hb e := by
  obtain ⟨e, hnot⟩ := p4Q2PZ37AAZ_exists_originalLink_centeredGIGap_notAEZero H b hb
  refine ⟨e, ?_⟩
  by_contra hn
  have hzero : (∫ z : Cfg × Cfg, (gap b hb.le f₀ e z) ^ 2 ∂outer) = 0 :=
    le_antisymm (le_of_not_gt hn) (p4Q2PZ37ACE_originalMoment_nonneg H b hb e)
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun z : Cfg × Cfg => sq_nonneg (gap b hb.le f₀ e z))
    (p4Q2PZ37ACE_originalGapSquare_integrable H b hb e)).mp hzero
  apply hnot
  filter_upwards [hae] with z hz
  change (gap b hb.le f₀ e z) ^ 2 = 0 at hz
  have hh : gap b hb.le f₀ e z * gap b hb.le f₀ e z = 0 := by
    simpa only [pow_two] using hz
  rcases mul_eq_zero.mp hh with h | h <;> exact h

/-- A finite cap constructed from the SAME original squared GI response.
It is not a new physical normalization or a volume-uniform constant. -/
def p4Q2PZ37ACE_originalGapSquareCap (b : ℝ) (hb : 0 < b) (e : Link) : ℝ :=
  ‖(⟨fun z : Cfg × Cfg => (gap b hb.le f₀ e z) ^ 2,
    (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le f₀ e).pow 2⟩ : C(Cfg × Cfg, ℝ))‖ + 1
local notation "K" => p4Q2PZ37ACE_originalGapSquareCap H

/-- The genuine compact cap is strictly positive even on a zero-response link. -/
theorem p4Q2PZ37ACE_originalGapSquareCap_pos
    (b : ℝ) (hb : 0 < b) (e : Link) : 0 < K b hb e := by
  unfold p4Q2PZ37ACE_originalGapSquareCap
  positivity

/-- No pointwise cap is postulated: it follows from the original continuous map. -/
theorem p4Q2PZ37ACE_originalGapSquare_le_cap
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Cfg × Cfg) :
    (gap b hb.le f₀ e z) ^ 2 ≤ K b hb e := by
  let B : C(Cfg × Cfg, ℝ) := ⟨fun w => (gap b hb.le f₀ e w) ^ 2,
    (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous H b hb.le f₀ e).pow 2⟩
  have h : |(gap b hb.le f₀ e z) ^ 2| ≤ ‖B‖ := by
    simpa only [Real.norm_eq_abs] using B.norm_coe_le_norm z
  rw [abs_of_nonneg (sq_nonneg _)] at h
  change (gap b hb.le f₀ e z) ^ 2 ≤ ‖B‖ + 1
  linarith only [h]

/-- The original upper event, defined without a common sign or a covariance assumption. -/
def p4Q2PZ37ACE_originalHalfMomentEvent
    (b : ℝ) (hb : 0 < b) (e : Link) : Set (Cfg × Cfg) :=
  {z | M b hb e / 2 < (gap b hb.le f₀ e z) ^ 2}
local notation "Event" => p4Q2PZ37ACE_originalHalfMomentEvent H

/-- A quantitative original Haar-mass bound for an open high-amplitude GI event. -/
theorem p4Q2PZ37ACE_originalHalfMomentEvent_mass_lower
    (b : ℝ) (hb : 0 < b) (e : Link) (hm : 0 < M b hb e) :
    IsOpen (Event b hb e) ∧
      M b hb e / (2 * K b hb e) ≤ Measure.real outer (Event b hb e) := by
  have hopen : IsOpen (Event b hb e) :=
    isOpen_lt continuous_const
      ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous H b hb.le f₀ e).pow 2)
  refine ⟨hopen, ?_⟩
  exact CompactProbabilityUpperEvent.halfMean_div_cap_le_mass outer
    (fun z : Cfg × Cfg => (gap b hb.le f₀ e z) ^ 2)
    (p4Q2PZ37ACE_originalGapSquare_integrable H b hb e) hm
    (K b hb e) (p4Q2PZ37ACE_originalGapSquareCap_pos H b hb e)
    (p4Q2PZ37ACE_originalGapSquare_le_cap H b hb e) hopen.measurableSet

/-- Unconditional finite-volume positive event mass with its actual M/(2*K)
certificate. All parameters retain their H,b dependence. -/
theorem p4Q2PZ37ACE_exists_originalPositiveMassEvent
    (b : ℝ) (hb : 0 < b) :
    ∃ e : Link, 0 < M b hb e ∧ IsOpen (Event b hb e) ∧
      0 < Measure.real outer (Event b hb e) ∧
      M b hb e / (2 * K b hb e) ≤ Measure.real outer (Event b hb e) := by
  obtain ⟨e, hm⟩ := p4Q2PZ37ACE_exists_originalMoment_pos H b hb
  have h := p4Q2PZ37ACE_originalHalfMomentEvent_mass_lower H b hb e hm
  have hp : 0 < M b hb e / (2 * K b hb e) :=
    div_pos hm (mul_pos (by norm_num) (p4Q2PZ37ACE_originalGapSquareCap_pos H b hb e))
  exact ⟨e, hm, h.1, hp.trans_le h.2, h.2⟩

/-- ACD's actual covariance/variance region yields a true physical Rayleigh
bound, retaining the independently required upper cap on the original FX law. -/
theorem p4Q2PZ37ACE_originalRayleigh_of_covarianceRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (S : Set (Cfg × Cfg)) (hS : MeasurableSet S) (c V q : ℝ) (hq : 0 < q)
    (hdelta : 0 ≤ Delta b c V)
    (hMoments : ∀ z ∈ S,
      c ≤ |Cov (F b hb.le f₀ e z) E| ∧ Var (F b hb.le f₀ e z) ≤ V)
    (hQcap : ∀ z : Cfg × Cfg,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb.le z.2 e ≤ q) :
    (Measure.real outer S * (Delta b c V) ^ 2 / q) / 18 ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  have hMoment := p4Q2PZ37ACD_originalOuterMoment_lower_of_momentRegion
    H b hb.le f₀ e S hS c V hdelta hMoments
  have hm : 0 ≤ Measure.real outer S * (Delta b c V) ^ 2 :=
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  apply p4Q2PZ37AAX2_originalRayleighFloor_of_rawSingleLink
    H b hb (Measure.real outer S * (Delta b c V) ^ 2 / q) (div_nonneg hm hq.le)
  refine ⟨e, ?_⟩
  exact p4Q2PZ37AAZ_originalRawResponse_ge_of_gapMoment H b hb e
    (Measure.real outer S * (Delta b c V) ^ 2) q hq hQcap
    (p4Q2PZ37ACE_originalGapSquare_integrable H b hb e) hMoment

/-- The exact family-level bridge. A common positive original event-moment
budget and genuine FX cap remain explicit unsolved analytic obligations. -/
theorem p4Q2PZ37ACE_allVolumes_Rayleigh_of_covarianceRegions
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (m q : ℝ) (hm : 0 < m) (hq : 0 < q)
    (e : ∀ n, PeriodicHypercubicEvenSpatialSliceLink n)
    (S : ∀ n, Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration n 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration n 2))
    (hS : ∀ n, MeasurableSet (S n)) (c V : ℕ → ℝ)
    (hdelta : ∀ n, 0 ≤ Delta (b n) (c n) (V n))
    (hMass : ∀ n, m ≤
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure n 2) (S n) *
        (Delta (b n) (c n) (V n)) ^ 2)
    (hMoments : ∀ n, ∀ z ∈ S n,
      c n ≤ |Cov (p4Q2PZ37ABZ_originalReceiverSection n (b n) (hb n).le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection n) (e n) z) E| ∧
      Var (p4Q2PZ37ABZ_originalReceiverSection n (b n) (hb n).le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection n) (e n) z) ≤ V n)
    (hQcap : ∀ n, ∀ z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration n 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration n 2,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        n (b n) (hb n).le z.2 (e n) ≤ q) :
    0 < (m / q) / 18 ∧ ∀ n, (m / q) / 18 ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor n (b n) (hb n) := by
  apply p4Q2PZ37AAZ_allVolumes_Rayleigh_of_trueUnweightedGIMoments b hb m q hm hq e hQcap
  · intro n
    exact p4Q2PZ37ACE_originalGapSquare_integrable n (b n) (hb n) (e n)
  · intro n
    exact (hMass n).trans (p4Q2PZ37ACD_originalOuterMoment_lower_of_momentRegion
      n (b n) (hb n).le (p4Q2PZ37ZW_originalCenteredPhysicalDirection n)
      (e n) (S n) (hS n) (c n) (V n) (hdelta n) (hMoments n))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_originalGapSquare_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_originalMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_exists_originalMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_originalGapSquareCap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_originalGapSquare_le_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_originalHalfMomentEvent_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_exists_originalPositiveMassEvent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_originalRayleigh_of_covarianceRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACE_allVolumes_Rayleigh_of_covarianceRegions
