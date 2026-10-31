import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMomentMassRayleighV5_PZ37ACE
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorWeakFrozenNoGoV5_JL

/-!
# P4-Q2-PZ37ACF — explicit original FX envelope and physical moment bounds

The CURRENT exact-source JL theorem bounds the SAME two interacting Wilson
posterior density contrast by q(b)=(exp(16*b)-exp(-16*b))^2, independently
of H, the actual link and the right configuration. Its current dependency
closure is checked again below, rather than relying on AAZ's historical
comment about inherited finite-incidence axioms.

Combine this genuine envelope with ACE's proved integrability to remove the
independent FX-cap premise from the original raw-response/Rayleigh bridges.
Every finite H,b>0 has an actual link with M>0 and
  0 < (M/q(b))/18 <= R_H(b).
On a family 0<b(H)<=B, a common original unweighted moment M>=m>0 suffices
for the explicit uniform centered-source floor (m/q(B))/18. ACD moment
regions give the same criterion without an extra posterior-variance cap.

This does not construct a common positive M, a nonzero energy-covariance
witness, a sufficiently small actual regression defect, full physical
Hilbert coercivity, a common positive-fine interval or a continuum theory.
The original Wilson model, centered Gauss-law source, genuine Perron
representative, physical transfer norm, both interacting posterior laws
and outer pair-Haar remain unchanged. The zero-coupling endpoint is not
used as a positive denominator. Existing files and assumptions are intact.
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
local instance p4Q2PZ37ACF_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACF_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACF_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACF_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACF_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A numerical envelope, not a replacement FX law or physical normalization. -/
def p4Q2PZ37ACF_originalFXEnvelope (b : ℝ) : ℝ :=
  (Real.exp (16 * b) - Real.exp (-16 * b)) ^ 2
local notation "q" => p4Q2PZ37ACF_originalFXEnvelope

/-- The scalar envelope is nonnegative even at the decoupled endpoint. -/
theorem p4Q2PZ37ACF_originalFXEnvelope_nonneg (b : ℝ) : 0 ≤ q b :=
  sq_nonneg _

/-- Positive original coupling gives a genuinely positive denominator. -/
theorem p4Q2PZ37ACF_originalFXEnvelope_pos (b : ℝ) (hb : 0 < b) : 0 < q b := by
  have hw : 0 < Real.exp (16 * b) - Real.exp (-16 * b) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  exact pow_pos hw 2

/-- Bounded nonnegative couplings share one explicit envelope q(B). -/
theorem p4Q2PZ37ACF_originalFXEnvelope_mono
    (b B : ℝ) (hb : 0 ≤ b) (hbB : b ≤ B) : q b ≤ q B := by
  have hw : 0 ≤ Real.exp (16 * b) - Real.exp (-16 * b) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hu : Real.exp (16 * b) ≤ Real.exp (16 * B) :=
    Real.exp_le_exp.mpr (by linarith)
  have hl : Real.exp (-16 * B) ≤ Real.exp (-16 * b) :=
    Real.exp_le_exp.mpr (by linarith)
  exact pow_le_pow_left₀ hw (sub_le_sub hu hl) 2

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "M" => p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H
local notation "J" => p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H
local notation "R" => p4Q2PZ37AAH_originalExactCenteredRayleighFloor H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "Delta" => p4Q2PZ37ACD_quantitativeCovarianceMargin
local instance p4Q2PZ37ACF_links : Fintype Link := Fintype.ofFinite _

/-- Reuse the genuine current JL envelope with its exact physical types.
The current dependency closure is explicitly printed at the end of this file. -/
theorem p4Q2PZ37ACF_originalFX_le_envelope
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb right e ≤ q b :=
  p4Q2JL_originalPosteriorContrastHaarSq_le_envelope H b hb right e

/-- No H/link/right-configuration cap hypothesis remains for 0<=b<=B. -/
theorem p4Q2PZ37ACF_originalFX_le_uniformEnvelope
    (b B : ℝ) (hb : 0 ≤ b) (hbB : b ≤ B) (right : Cfg) (e : Link) :
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H b hb right e ≤ q B :=
  (p4Q2PZ37ACF_originalFX_le_envelope H b hb right e).trans
    (p4Q2PZ37ACF_originalFXEnvelope_mono b B hb hbB)

/-- The original unweighted GI square moment is bounded by the explicit
physical FX envelope times the original raw two-posterior response. -/
theorem p4Q2PZ37ACF_originalMoment_le_envelope_mul_rawResponse
    (b : ℝ) (hb : 0 < b) (e : Link) : M b hb e ≤ q b * J b hb e := by
  exact p4Q2PZ37AAZ_originalGapMoment_le_FXCap_mul_rawResponse H b hb e (q b)
    (fun z => p4Q2PZ37ACF_originalFX_le_envelope H b hb.le z.2 e)
    (p4Q2PZ37ACE_originalGapSquare_integrable H b hb e)

/-- The explicit true posterior-response bound has no independent FX-cap premise. -/
theorem p4Q2PZ37ACF_originalRawResponse_ge_moment_div_envelope
    (b : ℝ) (hb : 0 < b) (e : Link) : M b hb e / q b ≤ J b hb e := by
  exact p4Q2PZ37AAZ_originalRawResponse_ge_of_gapMoment H b hb e
    (M b hb e) (q b) (p4Q2PZ37ACF_originalFXEnvelope_pos b hb)
    (fun z => p4Q2PZ37ACF_originalFX_le_envelope H b hb.le z.2 e)
    (p4Q2PZ37ACE_originalGapSquare_integrable H b hb e) le_rfl

/-- A genuine unweighted moment controls the SAME centered physical Rayleigh
floor. This is a single physical source, not all-source Hilbert coercivity. -/
theorem p4Q2PZ37ACF_originalRayleigh_ge_moment_div_envelope
    (b : ℝ) (hb : 0 < b) (e : Link) : (M b hb e / q b) / 18 ≤ R b hb := by
  apply p4Q2PZ37AAX2_originalRayleighFloor_of_rawSingleLink H b hb
    (M b hb e / q b)
    (div_nonneg (p4Q2PZ37ACE_originalMoment_nonneg H b hb e)
      (p4Q2PZ37ACF_originalFXEnvelope_pos b hb).le)
  exact ⟨e, p4Q2PZ37ACF_originalRawResponse_ge_moment_div_envelope H b hb e⟩

/-- The positive finite-volume moment is supplied by ACE, not postulated.
Its H,b dependence is retained, so this is not a uniform positive floor. -/
theorem p4Q2PZ37ACF_exists_positive_originalMomentRayleighBound
    (b : ℝ) (hb : 0 < b) :
    ∃ e : Link, 0 < (M b hb e / q b) / 18 ∧ (M b hb e / q b) / 18 ≤ R b hb := by
  obtain ⟨e, hm⟩ := p4Q2PZ37ACE_exists_originalMoment_pos H b hb
  exact ⟨e, div_pos (div_pos hm (p4Q2PZ37ACF_originalFXEnvelope_pos b hb))
    (by norm_num), p4Q2PZ37ACF_originalRayleigh_ge_moment_div_envelope H b hb e⟩

/-- ACD's actual moment-region estimate now uses the PROVED numerical FX
cap q(b), while keeping all original covariance/variance/margin premises. -/
theorem p4Q2PZ37ACF_originalRayleigh_of_covarianceRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (S : Set (Cfg × Cfg)) (hS : MeasurableSet S) (c V : ℝ)
    (hdelta : 0 ≤ Delta b c V)
    (hMoments : ∀ z ∈ S,
      c ≤ |Cov (F b hb.le f₀ e z) E| ∧ Var (F b hb.le f₀ e z) ≤ V) :
    (Measure.real outer S * (Delta b c V) ^ 2 / q b) / 18 ≤ R b hb := by
  exact p4Q2PZ37ACE_originalRayleigh_of_covarianceRegion H b hb e S hS
    c V (q b) (p4Q2PZ37ACF_originalFXEnvelope_pos b hb) hdelta hMoments
    (fun z => p4Q2PZ37ACF_originalFX_le_envelope H b hb.le z.2 e)

/-- A common ORIGINAL unweighted moment lower bound is the only remaining
microscopic input for this bounded-coupling centered-source criterion.
No common positive moment is asserted by this conditional theorem. -/
theorem p4Q2PZ37ACF_allVolumes_Rayleigh_of_originalMoments
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (B : ℝ) (hB : 0 < B) (hUpper : ∀ n, b n ≤ B)
    (m : ℝ) (hm : 0 < m)
    (e : ∀ n, PeriodicHypercubicEvenSpatialSliceLink n)
    (hMoment : ∀ n, m ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment n (b n) (hb n) (e n)) :
    0 < (m / q B) / 18 ∧ ∀ n, (m / q B) / 18 ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor n (b n) (hb n) := by
  apply p4Q2PZ37AAZ_allVolumes_Rayleigh_of_trueUnweightedGIMoments
    b hb m (q B) hm (p4Q2PZ37ACF_originalFXEnvelope_pos B hB) e
  · intro n z
    exact p4Q2PZ37ACF_originalFX_le_uniformEnvelope n (b n) B (hb n).le
      (hUpper n) z.2 (e n)
  · intro n
    exact p4Q2PZ37ACE_originalGapSquare_integrable n (b n) (hb n) (e n)
  · exact hMoment

/-- Actual covariance regions give the family criterion without any extra
FX-law bound. The common positive event-moment budget is still explicit. -/
theorem p4Q2PZ37ACF_allVolumes_Rayleigh_of_covarianceRegions
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (B : ℝ) (hB : 0 < B) (hUpper : ∀ n, b n ≤ B)
    (m : ℝ) (hm : 0 < m)
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
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection n) (e n) z) ≤ V n) :
    0 < (m / q B) / 18 ∧ ∀ n, (m / q B) / 18 ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor n (b n) (hb n) := by
  apply p4Q2PZ37ACE_allVolumes_Rayleigh_of_covarianceRegions
    b hb m (q B) hm (p4Q2PZ37ACF_originalFXEnvelope_pos B hB)
    e S hS c V hdelta hMass hMoments
  intro n z
  exact p4Q2PZ37ACF_originalFX_le_uniformEnvelope n (b n) B (hb n).le
    (hUpper n) z.2 (e n)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JL_originalPosteriorContrastHaarSq_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalFXEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalFXEnvelope_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalFXEnvelope_mono
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalFX_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalFX_le_uniformEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalMoment_le_envelope_mul_rawResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalRawResponse_ge_moment_div_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalRayleigh_ge_moment_div_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_exists_positive_originalMomentRayleighBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_originalRayleigh_of_covarianceRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_allVolumes_Rayleigh_of_originalMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACF_allVolumes_Rayleigh_of_covarianceRegions
