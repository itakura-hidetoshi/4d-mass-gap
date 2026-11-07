import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneCrossingHaarOrthogonalityV5_PZ37AHR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalQuarticWardVanishesV5_PW3
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHS — ORIGINAL crossing-quadratic Haar selection and second action moment

Use the original spatial SU(2) product Haar, original centered physical
ZW Gauss-law source, and the original complete one-slab Wilson action.

AHR proved the exact source/crossing one-link selection
  integral f_H(A)*Cross_H(A,B) = 0,
using the true four-edge plaquette geometry and center-flip Haar.

The pre-existing PZ-PW/PW3 modules proved that EACH original plaquette
trace is orthogonal to the SQUARE of the entire original crossing action.
AHR's source is exactly MINUS ONE HALF of the plaquette-character sum,
so the actual source times Cross_H(A,B)^2 also integrates to ZERO.

Hence every quadratic polynomial a+b*Cross+c*Cross² has TRUE centered
source Haar expectation zero, for arbitrary coefficients and boundary.

For the complete actual one-slab action
  S_H(A,B)=f_H(A)+(p_H+W_H(B))/2+Cross_H(A,B),
this implies its genuine source-weighted SECOND action moment equals
  integral f_H(A)^3 +(p_H+W_H(B))*V_H
       +2*integral f_H(A)^2*Cross_H(A,B).
This retains the *actual* noncanceled mixed square/crossing Haar
correlation. It is NOT assumed zero, positive, or replaceable by an
independent-link posterior.

No imaginary transfer signs, spectral gap, fixed beta0 threshold, or
continuum YM gap are claimed. No existing Lean, kernel, source, Haar
measure, root, pins or workflows are modified. All new proofs use
the exact original source/presentation and only standard Lean axioms.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHS_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHS_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHS_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHS_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHS_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H

local instance p4Q2PZ37AHS_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The TRUE original source-weighted crossing-square Haar integral
vanishes on every finite even spatial period and every original B.
This is PW3's existing two-crossing Ward cancellation, transported to
the independently verified exact ZW Gauss-law source f=-h by AHR/PW2. -/
theorem p4Q2PZ37AHS_originalSource_crossingSquareHaar_zero (B : Cfg) :
    (∫ A : Cfg, fCont A * (Cross A B)^2 ∂muH) = 0 := by
  have hSource (A : Cfg) : fCont A = -(h A) := by
    rw [p4Q2PZ37AHR_originalSource_eq_negHalfTrace H A,
      p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A]
    ring
  have hWard :
      (∫ A : Cfg, (Cross A B)^2 * h A ∂muH) = 0 :=
    p4Q2PW3_originalTwoCrossingCenteredHaar_zero H B
  calc
    (∫ A : Cfg, fCont A * (Cross A B)^2 ∂muH) =
        ∫ A : Cfg, -((Cross A B)^2 * h A) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [hSource A]
      ring
    _ = -(∫ A : Cfg, (Cross A B)^2 * h A ∂muH) := by
      rw [integral_neg]
    _ = 0 := by rw [hWard]; ring

/-- The already-proved original single-crossing Haar identity on the
exact continuous ZW source (not on a substituted positive source). -/
theorem p4Q2PZ37AHS_originalSource_crossingHaar_zero (B : Cfg) :
    (∫ A : Cfg, fCont A * Cross A B ∂muH) = 0 :=
  p4Q2PZ37AHR_originalCrossingCorrelation_zero H B

/-- Every genuinely original quadratic polynomial in the temporal
crossing action is orthogonal to the same true centered ZW source:
the constant term cancels by original Haar centering, the linear
term by AHR, and the quadratic term by PW3 plus AHR's identity. -/
theorem p4Q2PZ37AHS_originalSource_quadraticCrossingHaar_zero
    (B : Cfg) (a b c : ℝ) :
    (∫ A : Cfg,
      fCont A * (a + b * Cross A B + c * (Cross A B)^2) ∂muH) = 0 := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hc : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  have ha : Integrable (fun A : Cfg => a * fCont A) muH :=
    (continuous_const.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : Integrable (fun A : Cfg => b * (fCont A * Cross A B)) muH :=
    (continuous_const.mul (hf.mul hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcc : Integrable (fun A : Cfg =>
      c * (fCont A * (Cross A B)^2)) muH :=
    (continuous_const.mul (hf.mul (hc.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      fCont A * (a + b * Cross A B + c * (Cross A B)^2) =
        a * fCont A +
          (b * (fCont A * Cross A B) +
            c * (fCont A * (Cross A B)^2)) := by ring
  calc
    (∫ A : Cfg,
        fCont A * (a + b * Cross A B + c * (Cross A B)^2) ∂muH) =
      (∫ A : Cfg,
        a * fCont A +
          (b * (fCont A * Cross A B) +
            c * (fCont A * (Cross A B)^2)) ∂muH) := by
          apply integral_congr_ae
          filter_upwards with A
          exact hPoint A
    _ = (∫ A : Cfg, a * fCont A ∂muH) +
          ((∫ A : Cfg, b * (fCont A * Cross A B) ∂muH) +
            (∫ A : Cfg, c * (fCont A * (Cross A B)^2) ∂muH)) := by
          rw [integral_add ha (hb.add hcc), integral_add hb hcc]
    _ = a * (∫ A : Cfg, fCont A ∂muH) +
          (b * (∫ A : Cfg, fCont A * Cross A B ∂muH) +
            c * (∫ A : Cfg, fCont A * (Cross A B)^2 ∂muH)) := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
    _ = 0 := by
      rw [p4Q2PZ37AHP_originalSource_mean_zero H,
        p4Q2PZ37AHS_originalSource_crossingHaar_zero H B,
        p4Q2PZ37AHS_originalSource_crossingSquareHaar_zero H B]
      ring

/-- True third Haar moment of the original continuous Gauss-law source,
NOT the unknown third derivative of a hypothetical transfer operator. -/
def p4Q2PZ37AHS_originalSourceThirdHaarMoment : ℝ :=
  ∫ A : Cfg, (fCont A)^3 ∂muH

/-- True squared-source temporal-crossing moment. This is the authentic
still-unevaluated mixed second-order coefficient, and is never
postulated zero or signed. -/
def p4Q2PZ37AHS_originalSourceSquareCrossingHaarMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, (fCont A)^2 * Cross A B ∂muH

/-- Actual one-slab action SECOND moment weighted by the original signed
continuous Gauss-law source, with the original complete slab action S. -/
def p4Q2PZ37AHS_originalSecondFullActionHaarMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A * (S A B)^2 ∂muH

/-- Exact full-Wilson second-action source Haar moment decomposition:
the pure temporal crossing² contribution and the linear crossing ×
source contribution are rigorously ZERO, leaving the actual cubic
source moment, the real right spatial Wilson boundary action, and
the genuine source-square/crossing correlation. -/
theorem p4Q2PZ37AHS_originalSecondFullActionHaarMoment_eq (B : Cfg) :
    p4Q2PZ37AHS_originalSecondFullActionHaarMoment H B =
      p4Q2PZ37AHS_originalSourceThirdHaarMoment H +
        (pH + W B) * Vsrc +
        2 * p4Q2PZ37AHS_originalSourceSquareCrossingHaarMoment H B := by
  let d : ℝ := (pH + W B) / 2
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hc : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  have hCube : Integrable (fun A : Cfg => (fCont A)^3) muH :=
    (hf.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hVariance : Integrable (fun A : Cfg =>
      (pH + W B) * (fCont A)^2) muH :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMixed : Integrable (fun A : Cfg =>
      2 * ((fCont A)^2 * Cross A B)) muH :=
    (continuous_const.mul ((hf.pow 2).mul hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoly : Integrable (fun A : Cfg =>
      fCont A * (d^2 + (pH + W B) * Cross A B + (Cross A B)^2)) muH :=
    (hf.mul ((continuous_const.add (continuous_const.mul hc)).add
      (hc.pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hInitial (A : Cfg) :
      S A B = fCont A + d + Cross A B := by
    have hsource := p4Q2PZ37AGN_originalCenteredContinuous_eq H A
    have hWA : W A = 2 * fCont A + pH := by
      linarith only [hsource]
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    rw [hWA]
    dsimp [d]
    ring
  have hPoint (A : Cfg) :
      fCont A * (S A B)^2 =
        (((fCont A)^3 + (pH + W B) * (fCont A)^2) +
          2 * ((fCont A)^2 * Cross A B)) +
        fCont A * (d^2 + (pH + W B) * Cross A B + (Cross A B)^2) := by
    rw [hInitial A]
    dsimp [d]
    ring
  have hPolyZero :
      (∫ A : Cfg,
        fCont A * (d^2 + (pH + W B) * Cross A B + (Cross A B)^2)
          ∂muH) = 0 := by
    simpa only [one_mul] using
      (p4Q2PZ37AHS_originalSource_quadraticCrossingHaar_zero
        H B (d^2) (pH + W B) (1 : ℝ))
  have hFirst : Integrable (fun A : Cfg =>
      ((fCont A)^3 + (pH + W B) * (fCont A)^2) +
        2 * ((fCont A)^2 * Cross A B)) muH :=
    (hCube.add hVariance).add hMixed
  calc
    p4Q2PZ37AHS_originalSecondFullActionHaarMoment H B =
        (∫ A : Cfg,
          (((fCont A)^3 + (pH + W B) * (fCont A)^2) +
            2 * ((fCont A)^2 * Cross A B)) +
          fCont A * (d^2 + (pH + W B) * Cross A B + (Cross A B)^2)
          ∂muH) := by
      unfold p4Q2PZ37AHS_originalSecondFullActionHaarMoment
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = (∫ A : Cfg,
          ((fCont A)^3 + (pH + W B) * (fCont A)^2) +
            2 * ((fCont A)^2 * Cross A B) ∂muH) +
        (∫ A : Cfg, fCont A *
          (d^2 + (pH + W B) * Cross A B + (Cross A B)^2)
          ∂muH) := by
      rw [integral_add hFirst hPoly]
    _ = ((∫ A : Cfg, (fCont A)^3 ∂muH) +
          (∫ A : Cfg, (pH + W B) * (fCont A)^2 ∂muH) +
          (∫ A : Cfg, 2 * ((fCont A)^2 * Cross A B) ∂muH)) +
        0 := by
      rw [hPolyZero, integral_add (hCube.add hVariance) hMixed,
        integral_add hCube hVariance]
    _ = p4Q2PZ37AHS_originalSourceThirdHaarMoment H +
        (pH + W B) * Vsrc +
        2 * p4Q2PZ37AHS_originalSourceSquareCrossingHaarMoment H B := by
      rw [integral_const_mul, integral_const_mul]
      simp only [add_zero]
      rfl

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHS_originalSource_crossingSquareHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHS_originalSource_crossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHS_originalSource_quadraticCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHS_originalSecondFullActionHaarMoment_eq
