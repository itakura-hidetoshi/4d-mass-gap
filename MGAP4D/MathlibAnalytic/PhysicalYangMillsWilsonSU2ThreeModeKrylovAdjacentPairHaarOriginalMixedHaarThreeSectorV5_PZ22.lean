import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthResponseCancellationV5_PZ21
import Mathlib.Tactic

/-!
# P4-Q2-PZ22 — exact ORIGINAL Wilson mixed-potential Haar sector isolation

The authentic PZ21 mixed response V(B) integrates, over the original
finite-volume spatial SU(2) Haar, the ORIGINAL one-slab Wilson action
S(A,B)=w(A)+Cross(A,B)+w(B) against the fully proved physical
left Haar one-slab moments M1..M4.

This file expands the exact fifth-degree mixed Wilson polynomial
and proves the complete, non-surrogate SU(2) Haar identity

 V(B) = V_low(B) + 70 F32(B) + 30 F23(B) + 5 F14(B),

 F32(B) = ∫ w(A)^3 Cross(A,B)^2 dHaar(A),
 F23(B) = ∫ w(A)^2 Cross(A,B)^3 dHaar(A),
 F14(B) = ∫ w(A)   Cross(A,B)^4 dHaar(A).

The integrand V_low(B) is written EXPLICITLY as powers of the true
crossing field, with coefficient of Cross² at most quadratic in w(A),
coefficient of Cross³ at most linear in w(A), coefficient of Cross⁴
an original Haar constant, and Cross¹ a Wilson gauge-invariant
spatial polynomial. This identifies exactly the remaining
higher-than-fourth total crossing/spatial SU(2) Haar sectors, with
the TRUE, previously proved lower Ward selection still applicable.

The original intermediate spatial plaquettes, BOTH Haar integrations,
true Wilson kernel, original Gauss-law source, and PZ21 sixth Ward
coefficient are unchanged. No assumption of independence,
rank-three, nonzero W6, nonzero witness, or Yang–Mills gap.
No new axiom, sorry/admit, Dobrushin or substitute posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ22_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ22_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ22_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ22_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ22_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ22_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section GenuineOriginalMixedHaarThreeSector
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "η3" => p4Q2PZ19_originalStrippedCubicHaarConstant H
local notation "η4" => p4Q2PZ20_originalStrippedFourthHaarConstant H
local notation "R" => p4Q2PZ21_originalMixedMomentPolynomial H
local notation "V" => p4Q2PZ21_originalMixedFifthBoundaryPotential H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

/-- The four ORIGINAL, already proved, one-slab Haar polynomials. -/
noncomputable def p4Q2PZ22_originalM1 (x : ℝ) : ℝ :=
  x + α
noncomputable def p4Q2PZ22_originalM2 (x : ℝ) : ℝ :=
  x^2 + 2*α*x + θ
noncomputable def p4Q2PZ22_originalM3 (x : ℝ) : ℝ :=
  x^3 + 3*α*x^2 + 3*θ*x + η3
noncomputable def p4Q2PZ22_originalM4 (x : ℝ) : ℝ :=
  x^4 + 4*α*x^3 + 6*θ*x^2 + 4*η3*x + η4

local notation "m1" => p4Q2PZ22_originalM1 H
local notation "m2" => p4Q2PZ22_originalM2 H
local notation "m3" => p4Q2PZ22_originalM3 H
local notation "m4" => p4Q2PZ22_originalM4 H

/-- Genuine mixed fifth polynomial, with exactly the source SU(2)
left Haar Wilson moments PZ17–PZ20, not a proposed test function. -/
noncomputable def p4Q2PZ22_originalMixedScalarPolynomial
    (x t : ℝ) : ℝ :=
  5*m4 x*t + 10*m3 x*t^2 + 10*m2 x*t^3 + 5*m1 x*t^4

local notation "Q" => p4Q2PZ22_originalMixedScalarPolynomial H

/-- The exact first-crossing Wilson coefficient; its dependence on
the spatial source x is gauge invariant for each fixed y. -/
noncomputable def p4Q2PZ22_originalSelectedCrossingOne
    (x y : ℝ) : ℝ :=
  5*m4 x + 20*m3 x*(x+y) +
    30*m2 x*(x+y)^2 + 20*m1 x*(x+y)^3

/-- After removing the unique degree-five x³ Crossing² term,
the exact second-crossing coefficient is only quadratic in x. -/
noncomputable def p4Q2PZ22_originalSelectedCrossingTwo
    (x y : ℝ) : ℝ :=
  10*(3*α*y^2 + η3 + 3*θ*y) +
    10*(12*α*y + 6*θ + 3*y^2)*x +
    10*(12*α+9*y)*x^2

/-- After removing the degree-five x² Crossing³ term,
the true third-crossing coefficient is only linear in x. -/
noncomputable def p4Q2PZ22_originalSelectedCrossingThree
    (x y : ℝ) : ℝ :=
  10*(2*α*y + θ) + 10*(4*α+2*y)*x

local notation "P1" => p4Q2PZ22_originalSelectedCrossingOne H
local notation "P2" => p4Q2PZ22_originalSelectedCrossingTwo H
local notation "P3" => p4Q2PZ22_originalSelectedCrossingThree H

/-- A universal, exact algebraic identity for the ORIGINAL physical
fifth mixed Wilson action after separation into its lower Ward and
three genuine degree-five weighted-crossing sectors. -/
theorem p4Q2PZ22_originalMixedScalar_threeHighSector
    (x c y : ℝ) :
    Q x (x+c+y) =
      ((((Q x (x+y) + P1 x y*c) +
        P2 x y*c^2) +
        P3 x y*c^3) +
        5*α*c^4) +
      ((70*x^3*c^2 + 30*x^2*c^3) + 5*x*c^4) := by
  simp only [p4Q2PZ22_originalMixedScalarPolynomial,
    p4Q2PZ22_originalSelectedCrossingOne,
    p4Q2PZ22_originalSelectedCrossingTwo,
    p4Q2PZ22_originalSelectedCrossingThree,
    p4Q2PZ22_originalM1, p4Q2PZ22_originalM2,
    p4Q2PZ22_originalM3, p4Q2PZ22_originalM4]
  ring

/-- Every moment input is from the real original one-slab SU(2)
Haar, at the actual intermediate spatial Wilson configuration. -/
theorem p4Q2PZ22_originalMixedPhysical_eq_scalar
    (A B : Cfg) :
    R A (S A B) =
      Q (w A) (w A + Cross A B + w B) := by
  rw [p4Q2PZ21_originalMixedPolynomial_spatialWilson H A (S A B)]
  rw [p4Q2PS_originalOneSlabAction_rightSplit H A B]
  unfold p4Q2PS_originalRightStrippedAction
    p4Q2PZ22_originalMixedScalarPolynomial
    p4Q2PZ22_originalM1 p4Q2PZ22_originalM2
    p4Q2PZ22_originalM3 p4Q2PZ22_originalM4
  ring

/-- The source-preserving low Ward sector, with all subcritical
real SU(2) Haar weights given explicitly (no independence). -/
noncomputable def p4Q2PZ22_originalSelectedLowIntegrand
    (A B : Cfg) : ℝ :=
  let x := w A
  let y := w B
  let c := Cross A B
  ((((Q x (x+y) + P1 x y*c) +
    P2 x y*c^2) +
    P3 x y*c^3) +
    5*α*c^4)

/-- Exactly the THREE genuinely higher-weight original Haar
integrands, with their combinatorial 70/30/5 multiplicities. -/
noncomputable def p4Q2PZ22_originalThreeHighIntegrand
    (A B : Cfg) : ℝ :=
  let x := w A
  let c := Cross A B
  (70*x^3*c^2 + 30*x^2*c^3) + 5*x*c^4

local notation "Low" => p4Q2PZ22_originalSelectedLowIntegrand H
local notation "High" => p4Q2PZ22_originalThreeHighIntegrand H

/-- Every point of the ORIGINAL physical SU(2) outer Haar sample
retains its full Wilson action, split into the selected lower
and the three genuine degree-five crossing sectors. -/
theorem p4Q2PZ22_originalMixedIntegrand_threeHighSector
    (A B : Cfg) :
    R A (S A B) = Low A B + High A B := by
  rw [p4Q2PZ22_originalMixedPhysical_eq_scalar H A B]
  exact p4Q2PZ22_originalMixedScalar_threeHighSector H
    (w A) (Cross A B) (w B)

/-- Lower-Ward original Haar profile; not presumed independent
of B until all its individual Ward selection rules are applied. -/
noncomputable def p4Q2PZ22_originalSelectedLowHaarPotential
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, Low A B ∂haar

/-- Physical three higher-than-fourth degree Haar crossing sectors. -/
noncomputable def p4Q2PZ22_originalSpatialCubeCrossingSquareHaar
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, (w A)^3 * (Cross A B)^2 ∂haar

noncomputable def p4Q2PZ22_originalSpatialSquareCrossingCubeHaar
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, (w A)^2 * (Cross A B)^3 ∂haar

noncomputable def p4Q2PZ22_originalSpatialCrossingFourthHaar
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, w A * (Cross A B)^4 ∂haar

local notation "Vlo" => p4Q2PZ22_originalSelectedLowHaarPotential H
local notation "F32" => p4Q2PZ22_originalSpatialCubeCrossingSquareHaar H
local notation "F23" => p4Q2PZ22_originalSpatialSquareCrossingCubeHaar H
local notation "F14" => p4Q2PZ22_originalSpatialCrossingFourthHaar H

private theorem p4Q2PZ22_half_continuous :
    Continuous (fun A : Cfg => w A) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ22_cross_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Cross A B) := by
  have hp : Continuous (fun A : Cfg => (A,B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

private theorem p4Q2PZ22_low_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Low A B) := by
  have hw := p4Q2PZ22_half_continuous H
  have hc := p4Q2PZ22_cross_continuous H B
  unfold p4Q2PZ22_originalSelectedLowIntegrand
    p4Q2PZ22_originalMixedScalarPolynomial
    p4Q2PZ22_originalSelectedCrossingOne
    p4Q2PZ22_originalSelectedCrossingTwo
    p4Q2PZ22_originalSelectedCrossingThree
    p4Q2PZ22_originalM1 p4Q2PZ22_originalM2
    p4Q2PZ22_originalM3 p4Q2PZ22_originalM4
  fun_prop (disch := assumption)

private theorem p4Q2PZ22_high_continuous (B : Cfg) :
    Continuous (fun A : Cfg => High A B) := by
  have hw := p4Q2PZ22_half_continuous H
  have hc := p4Q2PZ22_cross_continuous H B
  unfold p4Q2PZ22_originalThreeHighIntegrand
  fun_prop (disch := assumption)

/-- Original Haar integral of the three high sectors has precisely
the true combinatorial coefficients, with NO posterior product. -/
theorem p4Q2PZ22_originalThreeHighHaar_exact
    (B : Cfg) :
    (∫ A : Cfg, High A B ∂haar) =
      70*F32 B + 30*F23 B + 5*F14 B := by
  have hw := p4Q2PZ22_half_continuous H
  have hc := p4Q2PZ22_cross_continuous H B
  have h1 : Integrable
      (fun A : Cfg => 70*(w A)^3*(Cross A B)^2) haar :=
    ((continuous_const.mul (hw.pow 3)).mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable
      (fun A : Cfg => 30*(w A)^2*(Cross A B)^3) haar :=
    ((continuous_const.mul (hw.pow 2)).mul (hc.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h3 : Integrable
      (fun A : Cfg => 5*w A*(Cross A B)^4) haar :=
    ((continuous_const.mul hw).mul (hc.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ A : Cfg,
      (70*(w A)^3*(Cross A B)^2 +
        30*(w A)^2*(Cross A B)^3) +
        5*w A*(Cross A B)^4 ∂haar) =
      70*(∫ A : Cfg, (w A)^3*(Cross A B)^2 ∂haar) +
        30*(∫ A : Cfg, (w A)^2*(Cross A B)^3 ∂haar) +
        5*(∫ A : Cfg, w A*(Cross A B)^4 ∂haar)
  have hAdd12 :
      (∫ A : Cfg,
        70*(w A)^3*(Cross A B)^2 +
          30*(w A)^2*(Cross A B)^3 ∂haar) =
      (∫ A : Cfg, 70*(w A)^3*(Cross A B)^2 ∂haar) +
        (∫ A : Cfg, 30*(w A)^2*(Cross A B)^3 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add h1 h2)
  have hAdd123 :
      (∫ A : Cfg,
        (70*(w A)^3*(Cross A B)^2 +
          30*(w A)^2*(Cross A B)^3) +
          5*w A*(Cross A B)^4 ∂haar) =
      (∫ A : Cfg,
        70*(w A)^3*(Cross A B)^2 +
          30*(w A)^2*(Cross A B)^3 ∂haar) +
        (∫ A : Cfg, 5*w A*(Cross A B)^4 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (h1.add h2) h3)
  calc
    (∫ A : Cfg,
      (70*(w A)^3*(Cross A B)^2 +
        30*(w A)^2*(Cross A B)^3) +
        5*w A*(Cross A B)^4 ∂haar) =
        (∫ A : Cfg,
          70*(w A)^3*(Cross A B)^2 +
            30*(w A)^2*(Cross A B)^3 ∂haar) +
          (∫ A : Cfg, 5*w A*(Cross A B)^4 ∂haar) := hAdd123
    _ = (∫ A : Cfg, 70*(w A)^3*(Cross A B)^2 ∂haar) +
          (∫ A : Cfg, 30*(w A)^2*(Cross A B)^3 ∂haar) +
          (∫ A : Cfg, 5*w A*(Cross A B)^4 ∂haar) := by
            rw [hAdd12]
    _ = 70*(∫ A : Cfg, (w A)^3*(Cross A B)^2 ∂haar) +
          30*(∫ A : Cfg, (w A)^2*(Cross A B)^3 ∂haar) +
          5*(∫ A : Cfg, w A*(Cross A B)^4 ∂haar) := by
            simp only [mul_assoc, integral_const_mul]

/-- PZ21's original mixed potential consists EXACTLY of the
explicit selected lower-Ward Haar integral plus THREE true Wilson
weighted-crossing moments, not a fictitious spectral measure. -/
theorem p4Q2PZ22_originalMixedPotential_threeHighHaar
    (B : Cfg) :
    V B = Vlo B + 70*F32 B + 30*F23 B + 5*F14 B := by
  have hlo : Integrable (fun A : Cfg => Low A B) haar :=
    (p4Q2PZ22_low_continuous H B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hhi : Integrable (fun A : Cfg => High A B) haar :=
    (p4Q2PZ22_high_continuous H B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold p4Q2PZ21_originalMixedFifthBoundaryPotential
  calc
    (∫ A : Cfg, R A (S A B) ∂haar) =
        ∫ A : Cfg, Low A B + High A B ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact p4Q2PZ22_originalMixedIntegrand_threeHighSector H A B
    _ = Vlo B + (∫ A : Cfg, High A B ∂haar) := by
      rw [integral_add hlo hhi]
      rfl
    _ = Vlo B + 70*F32 B + 30*F23 B + 5*F14 B := by
      rw [p4Q2PZ22_originalThreeHighHaar_exact H B]
      ring

/-- The fully genuine sixth Ward obstruction now has exactly three
unselected higher-weight original SU(2) crossing sectors in its
original mixed Haar potential. This is an equality, not a rank or
nonzero witness statement. -/
theorem p4Q2PZ22_originalSixthWard_threeHighHaar
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C -
      6*((a B-a A)*
          ((Vlo C-Vlo A)+70*(F32 C-F32 A)+
            30*(F23 C-F23 A)+5*(F14 C-F14 A)) -
        (a C-a A)*
          ((Vlo B-Vlo A)+70*(F32 B-F32 A)+
            30*(F23 B-F23 A)+5*(F14 B-F14 A))) := by
  rw [p4Q2PZ21_originalSixthWard_mixedPotential H A B C,
    p4Q2PZ22_originalMixedPotential_threeHighHaar H A,
    p4Q2PZ22_originalMixedPotential_threeHighHaar H B,
    p4Q2PZ22_originalMixedPotential_threeHighHaar H C]
  ring

end GenuineOriginalMixedHaarThreeSector
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ22_originalMixedScalar_threeHighSector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ22_originalMixedPhysical_eq_scalar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ22_originalMixedIntegrand_threeHighSector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ22_originalThreeHighHaar_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ22_originalMixedPotential_threeHighHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ22_originalSixthWard_threeHighHaar
