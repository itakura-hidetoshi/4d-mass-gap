import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGaugeWardAffineSecondMomentV5_PZ37AHT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHU — exact original gauge-Ward center evaluation of mixed Haar moment

AHT had proved that the genuine continuous squared-source mixed
Haar correlation is right-boundary independent, but did not evaluate it.

The actual SU(2) central element z=-I obeys E(g*z)=2-E(g) for the
ORIGINAL normalized Wilson link energy. PT already proves, with NO
factorization assumption, that a continuous gauge-invariant observable
phi has a crossing-link Haar integral independent of the right
boundary. Compare the original PT integral at the TRUE identity and
at the TRUE central configuration z; linearity gives its exact value:

  integral phi(A)*E((A_e)^-1*B_e) dmu = integral phi(A) dmu.

Summing over all original crossing links (whose count equals p_H by
the independently verified AHI identity) gives

  integral phi(A)*Cross_H(A,B) dmu = p_H*integral phi(A) dmu.

Apply this to phi=f_H(A)^2, already proved continuous and gauge-invariant
in AHT, to evaluate the AHS true mixed moment without replacing the
original spatial Haar probability or postulating independence:

  Y_H(B)=p_H*V_H,  V_H=integral f_H(A)^2 dmu.

Consequently the original AHT affine intercept is exactly
M3_H+3*p_H*V_H, leaving only the GENUINE source cubic Haar moment
M3_H unevaluated. The complete original one-slab second moment is

  M2_H(B)=M3_H+(3*p_H+W_H(B))*V_H.

Everything is an identity in the original finite-volume SU(2) Wilson
source/action and the true gauge-preserving product Haar measure.
No unproved numerical cubic evaluation, original fixed-beta0 sign,
H-uniform coercivity, Hamiltonian gap or continuum 4D YM mass gap.
Append-only one new Lean leaf; all previous physical models, typed
source histories, source files, roots, pins and workflows are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "z" => specialUnitaryTwoNegativeIdentity
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Y" => p4Q2PZ37AHS_originalSourceSquareCrossingHaarMoment H
local notation "M3" => p4Q2PZ37AHS_originalSourceThirdHaarMoment H
local notation "M2" => p4Q2PZ37AHS_originalSecondFullActionHaarMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2

local instance p4Q2PZ37AHU_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHU_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Exact one-link original Wilson Haar expectation under ANY original
continuous gauge-invariant weight. The SU(2) central identity plus PT's
proved genuine gauge Ward symmetry suffice; no measure independence. -/
theorem p4Q2PZ37AHU_originalGaugeWeight_singleLinkHaar_exact
    (φ : Cfg → ℝ) (hφ : Continuous φ)
    (hGauge : ∀ (γ : Gauge) (A : Cfg),
      φ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
        φ A)
    (e : Link) (B : Cfg) :
    (∫ A : Cfg, φ A * E ((A e)⁻¹ * B e) ∂muH) =
      (∫ A : Cfg, φ A ∂muH) := by
  have hE : Continuous (fun A : Cfg => E ((A e)⁻¹)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv)
  have hφInt : Integrable φ muH :=
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWeightedInt :
      Integrable (fun A : Cfg => φ A * E ((A e)⁻¹)) muH :=
    (hφ.mul hE).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCenter :
      (∫ A : Cfg, φ A * E ((A e)⁻¹ * z) ∂muH) =
        (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂muH) := by
    simpa using (p4Q2PT_originalGaugeWeight_singleLinkHaar_invariant
      H φ hφ hGauge e (fun _ : Link => z))
  have hCenterExpansion :
      (∫ A : Cfg, φ A * E ((A e)⁻¹ * z) ∂muH) =
        2 * (∫ A : Cfg, φ A ∂muH) -
          (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂muH) := by
    calc
      (∫ A : Cfg, φ A * E ((A e)⁻¹ * z) ∂muH) =
          ∫ A : Cfg, 2 * φ A - φ A * E ((A e)⁻¹) ∂muH := by
        apply integral_congr_ae
        filter_upwards with A
        rw [specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
        ring
      _ = (∫ A : Cfg, 2 * φ A ∂muH) -
          (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂muH) := by
        rw [integral_sub (hφInt.const_mul 2) hWeightedInt]
      _ = 2 * (∫ A : Cfg, φ A ∂muH) -
          (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂muH) := by
        rw [integral_const_mul]
  have hMean :
      (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂muH) =
        (∫ A : Cfg, φ A ∂muH) := by
    rw [hCenterExpansion] at hCenter
    linarith only [hCenter]
  exact (p4Q2PT_originalGaugeWeight_singleLinkHaar_invariant
    H φ hφ hGauge e B).trans hMean

/-- Full ORIGINAL crossing action, not a proxy: exact weighted Haar
mean equals the actual number of original crossing links times the
original gauge-invariant Haar weight mean. -/
theorem p4Q2PZ37AHU_originalGaugeWeight_crossingHaar_exact
    (φ : Cfg → ℝ) (hφ : Continuous φ)
    (hGauge : ∀ (γ : Gauge) (A : Cfg),
      φ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
        φ A)
    (B : Cfg) :
    (∫ A : Cfg, φ A * Cross A B ∂muH) =
      pH * (∫ A : Cfg, φ A ∂muH) := by
  classical
  have hEnergy (e : Link) :
      Continuous (fun A : Cfg => E ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e : Link) :
      Integrable (fun A : Cfg => φ A * E ((A e)⁻¹ * B e)) muH :=
    (hφ.mul (hEnergy e)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCard : (Fintype.card Link : ℝ) = pH :=
    p4Q2PZ37AHI_cardLinks_eq_plaquettes H
  calc
    (∫ A : Cfg, φ A * Cross A B ∂muH) =
        ∫ A : Cfg, ∑ e : Link, φ A * E ((A e)⁻¹ * B e) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW_originalCrossing_eq_finsetSum H A B, Finset.mul_sum]
    _ = ∑ e : Link,
          (∫ A : Cfg, φ A * E ((A e)⁻¹ * B e) ∂muH) := by
      rw [integral_finset_sum _ (fun e _ => hEach e)]
    _ = ∑ _e : Link, (∫ A : Cfg, φ A ∂muH) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact p4Q2PZ37AHU_originalGaugeWeight_singleLinkHaar_exact
        H φ hφ hGauge e B
    _ = pH * (∫ A : Cfg, φ A ∂muH) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hCard]

/-- Exact numerical (in original plaquette-count and source-variance
scalars) value of AHS's genuine previously unevaluated mixed Haar
correlation. This is a Ward+central-element theorem, NOT factorization. -/
theorem p4Q2PZ37AHU_originalMixedCrossing_exact
    (B : Cfg) :
    Y B = pH * Vsrc := by
  change (∫ A : Cfg, (fCont A)^2 * Cross A B ∂muH) =
    pH * (∫ A : Cfg, (fCont A)^2 ∂muH)
  exact p4Q2PZ37AHU_originalGaugeWeight_crossingHaar_exact H
    (fun A : Cfg => (fCont A)^2)
    (p4Q2PZ37AHT_originalSourceSquare_continuous H)
    (p4Q2PZ37AHT_originalSourceSquare_gaugeInvariant H) B

/-- The formerly unevaluated AHT affine intercept is fully reduced to
the TRUE source cubic Haar moment and the known second source moment. -/
theorem p4Q2PZ37AHU_originalSecondMomentIntercept_exactMixed :
    p4Q2PZ37AHT_originalSecondMomentIntercept H =
      M3 + 3 * pH * Vsrc := by
  unfold p4Q2PZ37AHT_originalSecondMomentIntercept
  rw [p4Q2PZ37AHU_originalMixedCrossing_exact H (fun _ => 1)]
  ring

/-- Complete ORIGINAL SU(2) one-slab second source-weighted Wilson
moment, with the exact genuine mixed Haar correlation substituted.
Only the actual spatial source cubic Haar integral remains unknown. -/
theorem p4Q2PZ37AHU_originalSecondFullActionMoment_exactMixed
    (B : Cfg) :
    M2 B = M3 + (3 * pH + W B) * Vsrc := by
  rw [p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H B,
    p4Q2PZ37AHU_originalSecondMomentIntercept_exactMixed H]
  ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHU_originalGaugeWeight_singleLinkHaar_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHU_originalGaugeWeight_crossingHaar_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHU_originalMixedCrossing_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHU_originalSecondMomentIntercept_exactMixed
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHU_originalSecondFullActionMoment_exactMixed
