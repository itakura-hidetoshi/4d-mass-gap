import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMixedHaarThreeSectorV5_PZ22
import Mathlib.Tactic

/-!
# P4-Q2-PZ23 — genuine Wilson low-sector Haar Ward boundary profile

Continue the exact PZ22 original SU(2) mixed-potential identity
  V(B) = V_low(B) + 70 F32(B) + 30 F23(B) + 5 F14(B).

The PZ22 low sector is a sum of four spatial-crossing sectors and a
pure spatial term. Their Haar selection is now PROVED using:
* PT's arbitrary continuous gauge-invariant weight at crossing degree 1;
* PY6, PZ19 and PZ20's original weighted square-crossing Haar selection;
* PZ20's original weighted cube-crossing Haar selection;
* PZ19's actual SU(2) Haar left translation at degree 4.

For every physical boundary B, V_low(B) equals a single fixed Haar
profile evaluated at the original boundary half-spatial Wilson action
w(B). This is a literal equality on original spatial slice Haar, with
the genuine intermediate Wilson plaquettes still in every integrand.

The three degree-five mixed sectors remain exact UNSELECTED physical
Haar moments. The theorem gives the precise criterion for their
residual boundary dependence at equal spatial Wilson action. It
does NOT assert that any is nonconstant, that W6 is nonzero, or that a
rank-3 witness/mass gap exists. No independent posterior, new axiom,
sorry/admit, Dobrushin shortcut or substitute Hamiltonian.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ23_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ23_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ23_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ23_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ23_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ23_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section GenuineOriginalLowHaarWard
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "η3" => p4Q2PZ19_originalStrippedCubicHaarConstant H
local notation "Q" => p4Q2PZ22_originalMixedScalarPolynomial H
local notation "P1" => p4Q2PZ22_originalSelectedCrossingOne H
local notation "P2" => p4Q2PZ22_originalSelectedCrossingTwo H
local notation "P3" => p4Q2PZ22_originalSelectedCrossingThree H
local notation "V" => p4Q2PZ21_originalMixedFifthBoundaryPotential H
local notation "Vlo" => p4Q2PZ22_originalSelectedLowHaarPotential H
local notation "F32" => p4Q2PZ22_originalSpatialCubeCrossingSquareHaar H
local notation "F23" => p4Q2PZ22_originalSpatialSquareCrossingCubeHaar H
local notation "F14" => p4Q2PZ22_originalSpatialCrossingFourthHaar H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

private theorem p4Q2PZ23_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ23_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

/-- All polynomial functions of the original spatial Wilson half-action
are legal PT Ward weights. Here P1 is the exact PZ22 crossing-one
coefficient, including its true cubic and quartic spatial terms. -/
theorem p4Q2PZ23_originalSelectedCrossingOne_Haar_invariant
    (y : ℝ) (B : Cfg) :
    (∫ X : Cfg, P1 (w X) y * Cross X B ∂haar) =
      (∫ X : Cfg, P1 (w X) y * Cross X (fun _ => 1) ∂haar) := by
  have hw := p4Q2PZ23_half_continuous H
  have hp : Continuous (fun X : Cfg => P1 (w X) y) := by
    unfold p4Q2PZ22_originalSelectedCrossingOne
      p4Q2PZ22_originalM1 p4Q2PZ22_originalM2
      p4Q2PZ22_originalM3 p4Q2PZ22_originalM4
    fun_prop (disch := assumption)
  have hGauge (γ : Gauge) (X : Cfg) :
      w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X) = w X := by
    unfold p4Q2PS_originalHalfSpatialAction
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ X]
  have hInv : ∀ (γ : Gauge) (X : Cfg),
      P1 (w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X)) y = P1 (w X) y := by
    intro γ X
    rw [hGauge γ X]
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant
    H (fun X : Cfg => P1 (w X) y) hp hInv B

/-- Linearity of genuine SU(2) Haar for a quadratic spatial weight;
all constituent functions are continuous on the compact Haar domain. -/
private theorem p4Q2PZ23_quadraticCrossingSquare_integral
    (u v t : ℝ) (B : Cfg) :
    (∫ X : Cfg,
      (u + v*w X + t*(w X)^2)*(Cross X B)^2 ∂haar) =
      u*(∫ X : Cfg, (Cross X B)^2 ∂haar) +
      v*(∫ X : Cfg, w X*(Cross X B)^2 ∂haar) +
      t*(∫ X : Cfg, (w X)^2*(Cross X B)^2 ∂haar) := by
  have hw := p4Q2PZ23_half_continuous H
  have hc := p4Q2PZ23_cross_continuous H B
  have h0 : Integrable (fun X : Cfg => u*(Cross X B)^2) haar :=
    (continuous_const.mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun X : Cfg => v*(w X*(Cross X B)^2)) haar :=
    (continuous_const.mul (hw.mul (hc.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun X : Cfg => t*((w X)^2*(Cross X B)^2)) haar :=
    (continuous_const.mul ((hw.pow 2).mul (hc.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h01 :
      (∫ X : Cfg, u*(Cross X B)^2 +
        v*(w X*(Cross X B)^2) ∂haar) =
      (∫ X : Cfg, u*(Cross X B)^2 ∂haar) +
      (∫ X : Cfg, v*(w X*(Cross X B)^2) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add h0 h1)
  have h012 :
      (∫ X : Cfg,
        (u*(Cross X B)^2 + v*(w X*(Cross X B)^2)) +
          t*((w X)^2*(Cross X B)^2) ∂haar) =
      (∫ X : Cfg,
        u*(Cross X B)^2 + v*(w X*(Cross X B)^2) ∂haar) +
      (∫ X : Cfg, t*((w X)^2*(Cross X B)^2) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (h0.add h1) h2)
  calc
    (∫ X : Cfg,
      (u + v*w X + t*(w X)^2)*(Cross X B)^2 ∂haar) =
      ∫ X : Cfg,
        (u*(Cross X B)^2 + v*(w X*(Cross X B)^2)) +
          t*((w X)^2*(Cross X B)^2) ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        ring
    _ = u*(∫ X : Cfg, (Cross X B)^2 ∂haar) +
        v*(∫ X : Cfg, w X*(Cross X B)^2 ∂haar) +
        t*(∫ X : Cfg, (w X)^2*(Cross X B)^2 ∂haar) := by
      rw [h012, h01]
      simp only [integral_const_mul]

/-- The full PZ22 quadratic weight at crossing degree two is selected
by the existing original SU(2) square-crossing Ward theorems. -/
theorem p4Q2PZ23_originalSelectedCrossingTwo_Haar_invariant
    (y : ℝ) (B : Cfg) :
    (∫ X : Cfg, P2 (w X) y * (Cross X B)^2 ∂haar) =
      (∫ X : Cfg, P2 (w X) y * (Cross X (fun _ => 1))^2 ∂haar) := by
  let u : ℝ := 10*(3*α*y^2 + η3 + 3*θ*y)
  let v : ℝ := 10*(12*α*y + 6*θ + 3*y^2)
  let t : ℝ := 10*(12*α + 9*y)
  have hweight (x : ℝ) : P2 x y = u + v*x + t*x^2 := by
    unfold p4Q2PZ22_originalSelectedCrossingTwo
    dsimp [u,v,t]
  have hWard :
      (∫ X : Cfg, (u+v*w X+t*(w X)^2)*(Cross X B)^2 ∂haar) =
      (∫ X : Cfg,
        (u+v*w X+t*(w X)^2)*(Cross X (fun _ => 1))^2 ∂haar) := by
    rw [p4Q2PZ23_quadraticCrossingSquare_integral H u v t B,
      p4Q2PZ23_quadraticCrossingSquare_integral H u v t (fun _ => 1),
      p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 2 B,
      p4Q2PZ19_originalHalfSpatial_crossingSquareHaar_invariant H B,
      p4Q2PZ20_originalHalfSpatialSquare_crossingSquareHaar_invariant H B]
  calc
    (∫ X : Cfg, P2 (w X) y * (Cross X B)^2 ∂haar) =
      (∫ X : Cfg,
        (u+v*w X+t*(w X)^2)*(Cross X B)^2 ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      rw [hweight]
    _ = (∫ X : Cfg,
        (u+v*w X+t*(w X)^2)*(Cross X (fun _ => 1))^2 ∂haar) := hWard
    _ = (∫ X : Cfg,
        P2 (w X) y*(Cross X (fun _ => 1))^2 ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      rw [hweight]

private theorem p4Q2PZ23_linearCrossingCube_integral
    (u v : ℝ) (B : Cfg) :
    (∫ X : Cfg,
      (u + v*w X)*(Cross X B)^3 ∂haar) =
      u*(∫ X : Cfg, (Cross X B)^3 ∂haar) +
      v*(∫ X : Cfg, w X*(Cross X B)^3 ∂haar) := by
  have hw := p4Q2PZ23_half_continuous H
  have hc := p4Q2PZ23_cross_continuous H B
  have h0 : Integrable (fun X : Cfg => u*(Cross X B)^3) haar :=
    (continuous_const.mul (hc.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun X : Cfg => v*(w X*(Cross X B)^3)) haar :=
    (continuous_const.mul (hw.mul (hc.pow 3))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hadd :
      (∫ X : Cfg,
        u*(Cross X B)^3 + v*(w X*(Cross X B)^3) ∂haar) =
      (∫ X : Cfg, u*(Cross X B)^3 ∂haar) +
      (∫ X : Cfg, v*(w X*(Cross X B)^3) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add h0 h1)
  calc
    (∫ X : Cfg, (u+v*w X)*(Cross X B)^3 ∂haar) =
      (∫ X : Cfg,
        u*(Cross X B)^3 + v*(w X*(Cross X B)^3) ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      ring
    _ = u*(∫ X : Cfg, (Cross X B)^3 ∂haar) +
        v*(∫ X : Cfg, w X*(Cross X B)^3 ∂haar) := by
      rw [hadd]
      simp only [integral_const_mul]

theorem p4Q2PZ23_originalSelectedCrossingThree_Haar_invariant
    (y : ℝ) (B : Cfg) :
    (∫ X : Cfg, P3 (w X) y*(Cross X B)^3 ∂haar) =
      (∫ X : Cfg, P3 (w X) y*(Cross X (fun _ => 1))^3 ∂haar) := by
  let u : ℝ := 10*(2*α*y + θ)
  let v : ℝ := 10*(4*α + 2*y)
  have hweight (x : ℝ) : P3 x y = u + v*x := by
    unfold p4Q2PZ22_originalSelectedCrossingThree
    dsimp [u,v]
  have hWard :
      (∫ X : Cfg, (u+v*w X)*(Cross X B)^3 ∂haar) =
      (∫ X : Cfg, (u+v*w X)*(Cross X (fun _ => 1))^3 ∂haar) := by
    rw [p4Q2PZ23_linearCrossingCube_integral H u v B,
      p4Q2PZ23_linearCrossingCube_integral H u v (fun _ => 1),
      p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 3 B,
      p4Q2PZ20_originalHalfSpatial_crossingCubeHaar_invariant H B]
  calc
    (∫ X : Cfg, P3 (w X) y*(Cross X B)^3 ∂haar) =
      (∫ X : Cfg, (u+v*w X)*(Cross X B)^3 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        rw [hweight]
    _ = (∫ X : Cfg, (u+v*w X)*(Cross X (fun _ => 1))^3 ∂haar) := hWard
    _ = (∫ X : Cfg, P3 (w X) y*(Cross X (fun _ => 1))^3 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        rw [hweight]

theorem p4Q2PZ23_originalSelectedCrossingFour_Haar_invariant
    (B : Cfg) :
    (∫ X : Cfg, 5*α*(Cross X B)^4 ∂haar) =
      (∫ X : Cfg, 5*α*(Cross X (fun _ => 1))^4 ∂haar) := by
  simp only [integral_const_mul]
  rw [p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 4 B]

/-- The original low Ward integrand at an independent scalar boundary
parameter y. In the physical case y=w(B), this is definitionally the
PZ22 low sector; the crossing still uses the ACTUAL boundary B. -/
noncomputable def p4Q2PZ23_originalLowWardKernel
    (y : ℝ) (X B : Cfg) : ℝ :=
  ((((Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
      P2 (w X) y*(Cross X B)^2) +
      P3 (w X) y*(Cross X B)^3) +
      5*α*(Cross X B)^4)

/-- Fixed authentic SU(2) Haar profile at the identity crossing
configuration: only the ORIGINAL half-spatial Wilson boundary action
is substituted into its scalar variable. -/
noncomputable def p4Q2PZ23_originalLowWardBoundaryProfile (y : ℝ) : ℝ :=
  ∫ X : Cfg, p4Q2PZ23_originalLowWardKernel H y X (fun _ => 1) ∂haar

local notation "Klo" => p4Q2PZ23_originalLowWardKernel H
local notation "Profile" => p4Q2PZ23_originalLowWardBoundaryProfile H

/-- Exact linearity for the genuine continuous low Wilson Haar
integrand, with no assumed factorization. -/
private theorem p4Q2PZ23_lowHaar_fiveSector
    (y : ℝ) (B : Cfg) :
    (∫ X : Cfg, Klo y X B ∂haar) =
      (∫ X : Cfg, Q (w X) (w X+y) ∂haar) +
      (∫ X : Cfg, P1 (w X) y*Cross X B ∂haar) +
      (∫ X : Cfg, P2 (w X) y*(Cross X B)^2 ∂haar) +
      (∫ X : Cfg, P3 (w X) y*(Cross X B)^3 ∂haar) +
      (∫ X : Cfg, 5*α*(Cross X B)^4 ∂haar) := by
  have hw := p4Q2PZ23_half_continuous H
  have hc := p4Q2PZ23_cross_continuous H B
  have hq : Continuous (fun X : Cfg => Q (w X) (w X+y)) := by
    unfold p4Q2PZ22_originalMixedScalarPolynomial
      p4Q2PZ22_originalM1 p4Q2PZ22_originalM2
      p4Q2PZ22_originalM3 p4Q2PZ22_originalM4
    fun_prop (disch := assumption)
  have hp1 : Continuous (fun X : Cfg => P1 (w X) y) := by
    unfold p4Q2PZ22_originalSelectedCrossingOne
      p4Q2PZ22_originalM1 p4Q2PZ22_originalM2
      p4Q2PZ22_originalM3 p4Q2PZ22_originalM4
    fun_prop (disch := assumption)
  have hp2 : Continuous (fun X : Cfg => P2 (w X) y) := by
    unfold p4Q2PZ22_originalSelectedCrossingTwo
    fun_prop (disch := assumption)
  have hp3 : Continuous (fun X : Cfg => P3 (w X) y) := by
    unfold p4Q2PZ22_originalSelectedCrossingThree
    fun_prop (disch := assumption)
  have h0 : Integrable (fun X : Cfg => Q (w X) (w X+y)) haar :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun X : Cfg => P1 (w X) y*Cross X B) haar :=
    (hp1.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun X : Cfg => P2 (w X) y*(Cross X B)^2) haar :=
    (hp2.mul (hc.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 : Integrable (fun X : Cfg => P3 (w X) y*(Cross X B)^3) haar :=
    (hp3.mul (hc.pow 3)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h4 : Integrable (fun X : Cfg => 5*α*(Cross X B)^4) haar :=
    (continuous_const.mul (hc.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hadd01 :
      (∫ X : Cfg, Q (w X) (w X+y) +
          P1 (w X) y*Cross X B ∂haar) =
      (∫ X : Cfg, Q (w X) (w X+y) ∂haar) +
      (∫ X : Cfg, P1 (w X) y*Cross X B ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add h0 h1)
  have hadd012 :
      (∫ X : Cfg,
        (Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
          P2 (w X) y*(Cross X B)^2 ∂haar) =
      (∫ X : Cfg,
        Q (w X) (w X+y) + P1 (w X) y*Cross X B ∂haar) +
      (∫ X : Cfg, P2 (w X) y*(Cross X B)^2 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (h0.add h1) h2)
  have hadd0123 :
      (∫ X : Cfg,
        ((Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
          P2 (w X) y*(Cross X B)^2) +
          P3 (w X) y*(Cross X B)^3 ∂haar) =
      (∫ X : Cfg,
        (Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
          P2 (w X) y*(Cross X B)^2 ∂haar) +
      (∫ X : Cfg, P3 (w X) y*(Cross X B)^3 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add ((h0.add h1).add h2) h3)
  have hadd01234 :
      (∫ X : Cfg,
        (((Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
          P2 (w X) y*(Cross X B)^2) +
          P3 (w X) y*(Cross X B)^3) +
          5*α*(Cross X B)^4 ∂haar) =
      (∫ X : Cfg,
        ((Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
          P2 (w X) y*(Cross X B)^2) +
          P3 (w X) y*(Cross X B)^3 ∂haar) +
      (∫ X : Cfg, 5*α*(Cross X B)^4 ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add (((h0.add h1).add h2).add h3) h4)
  change (∫ X : Cfg,
      (((Q (w X) (w X+y) + P1 (w X) y*Cross X B) +
        P2 (w X) y*(Cross X B)^2) +
        P3 (w X) y*(Cross X B)^3) +
        5*α*(Cross X B)^4 ∂haar) = _
  rw [hadd01234, hadd0123, hadd012, hadd01]

/-- The exact physical selected low SU(2) Haar contribution factors
through the right boundary's original half-spatial Wilson action.
It is NOT assumed constant as B varies. -/
theorem p4Q2PZ23_originalSelectedLowHaar_eq_boundaryProfile
    (B : Cfg) :
    Vlo B = Profile (w B) := by
  have hDef :
      Vlo B = ∫ X : Cfg, Klo (w B) X B ∂haar := rfl
  rw [hDef, p4Q2PZ23_lowHaar_fiveSector H (w B) B]
  unfold p4Q2PZ23_originalLowWardBoundaryProfile
  rw [p4Q2PZ23_lowHaar_fiveSector H (w B) (fun _ => 1),
    p4Q2PZ23_originalSelectedCrossingOne_Haar_invariant H (w B) B,
    p4Q2PZ23_originalSelectedCrossingTwo_Haar_invariant H (w B) B,
    p4Q2PZ23_originalSelectedCrossingThree_Haar_invariant H (w B) B,
    p4Q2PZ23_originalSelectedCrossingFour_Haar_invariant H B]

/-- True Wilson potential: selected low profile, plus exactly the
three remaining ORIGINAL fifth-degree mixed crossing Haar sectors. -/
theorem p4Q2PZ23_originalMixedPotential_lowWardProfile
    (B : Cfg) :
    V B = Profile (w B) + 70*F32 B + 30*F23 B + 5*F14 B := by
  rw [p4Q2PZ22_originalMixedPotential_threeHighHaar H B,
    p4Q2PZ23_originalSelectedLowHaar_eq_boundaryProfile H B]

/-- On any fixed original boundary Wilson spatial-action level set,
the ENTIRE possible variation of V is carried by F32,F23,F14.
This asserts no nonvanishing or independence of those sectors. -/
theorem p4Q2PZ23_originalMixedPotential_sameSpatialAction_difference
    (B C : Cfg) (h : w B = w C) :
    V B - V C =
      70*(F32 B-F32 C) + 30*(F23 B-F23 C) +
        5*(F14 B-F14 C) := by
  rw [p4Q2PZ23_originalMixedPotential_lowWardProfile H B,
      p4Q2PZ23_originalMixedPotential_lowWardProfile H C, h]
  ring

/-- A precise, proved sufficient condition for no mixed-potential
variation on equal-spatial-action boundaries, not a blanket claim
that the higher SU(2) sectors satisfy it. -/
theorem p4Q2PZ23_originalMixedPotential_sameSpatialAction_invariant_of_high
    (B C : Cfg) (h : w B = w C)
    (h32 : F32 B = F32 C) (h23 : F23 B = F23 C)
    (h14 : F14 B = F14 C) :
    V B = V C := by
  have hdiff :=
    p4Q2PZ23_originalMixedPotential_sameSpatialAction_difference H B C h
  rw [h32, h23, h14] at hdiff
  linarith

/-- No change to the true sixth Ward obstruction or its 720*C6
coefficient. Only the previously unresolved high sectors remain
as non-spatial boundary effects in the exact PZ22 expression. -/
theorem p4Q2PZ23_originalSixthWard_lowWardProfile
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C -
      6*((a B-a A)*
          ((Profile (w C)-Profile (w A)) +
            70*(F32 C-F32 A)+30*(F23 C-F23 A)+5*(F14 C-F14 A)) -
        (a C-a A)*
          ((Profile (w B)-Profile (w A)) +
            70*(F32 B-F32 A)+30*(F23 B-F23 A)+5*(F14 B-F14 A))) := by
  rw [p4Q2PZ22_originalSixthWard_threeHighHaar H A B C,
    p4Q2PZ23_originalSelectedLowHaar_eq_boundaryProfile H A,
    p4Q2PZ23_originalSelectedLowHaar_eq_boundaryProfile H B,
    p4Q2PZ23_originalSelectedLowHaar_eq_boundaryProfile H C]

end GenuineOriginalLowHaarWard
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalSelectedCrossingOne_Haar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalSelectedCrossingTwo_Haar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalSelectedCrossingThree_Haar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalSelectedCrossingFour_Haar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalSelectedLowHaar_eq_boundaryProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalMixedPotential_lowWardProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalMixedPotential_sameSpatialAction_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalMixedPotential_sameSpatialAction_invariant_of_high
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ23_originalSixthWard_lowWardProfile