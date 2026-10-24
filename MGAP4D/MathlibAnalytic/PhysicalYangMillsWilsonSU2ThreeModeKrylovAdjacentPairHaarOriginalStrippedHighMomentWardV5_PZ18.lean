import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSelectedMomentWardV5_PZ17
import Mathlib.Tactic

/-!
# P4-Q2-PZ18 — genuine right-stripped higher Haar-moment Ward residue

The ORIGINAL Wilson action is S(X,A) = L(X,A) + w(A), where
L(X,A) = w(X) + Cross(X,A). The left spatial plaquettes and all
original temporal link crossings are unchanged. No posterior
independence or artificial reference action is introduced.

Direct original SU(2) Haar selection (IX, PY6 and PY6B) makes the
first two right-stripped raw moments equal to the genuine constants
alpha_H and theta_H, even at period two.

This file proves exact cubic and quartic *genuine Haar binomial*
expansions. All remaining higher boundary information is contained
in the truly interacting reference-Haar functions
  xi3(A) = integral_X L(X,A)^3, xi4(A) = integral_X L(X,A)^4.
The PZ17 selected fourth polarization consequently separates into
an explicit low-polynomial part and
  5 xi4(A) + (20 w(A)+10(t+u)) xi3(A).
This is a structural reduction, NOT a claim that xi3 or xi4 has
nonconstant boundary dependence, nor a sixth Ward nonzero witness.

The original outer Haar, true intermediate plaquettes, all original
SU(2) links and both genuine posterior sectors remain intact.
No new axioms, sorry/admit, Dobrushin, surrogate, or mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ18_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ18_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ18_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ18_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ18_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ18_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ18_productProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalStrippedHigherHaar

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
local notation "L" => p4Q2PS_originalRightStrippedAction H
local notation "M" => p4Q2PZ16_originalLeftSlabMoment H
local notation "K" => p4Q2PZ16_originalConditionalFourthTower H
local notation "P4" => p4Q2PZ15_originalFourthPolarization
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

private theorem p4Q2PZ18_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ18_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

private theorem p4Q2PZ18_stripped_continuous (B : Cfg) :
    Continuous (fun X : Cfg => L X B) := by
  change Continuous (fun X : Cfg => w X + Cross X B)
  exact (p4Q2PZ18_half_continuous H).add
    (p4Q2PZ18_cross_continuous H B)

/-- The truly Wilson right-stripped Haar moment; spatial plaquettes
at X and crossing interaction from X to A are both present. -/
noncomputable def p4Q2PZ18_originalStrippedHaarMoment
    (k : ℕ) (A : Cfg) : ℝ :=
  ∫ X : Cfg, (L X A)^k ∂haar

local notation "μ" => p4Q2PZ18_originalStrippedHaarMoment H

/-- Original SU(2) Haar one-crossing Ward selection yields an EXACT
boundary-independent first right-stripped moment. -/
theorem p4Q2PZ18_originalStrippedFirst_eq_alpha (A : Cfg) :
    μ 1 A = α := by
  have hiw : Integrable (fun X : Cfg => w X) haar :=
    (p4Q2PZ18_half_continuous H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hic : Integrable (fun X : Cfg => Cross X A) haar :=
    (p4Q2PZ18_cross_continuous H A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    μ 1 A = ∫ X : Cfg, w X + Cross X A ∂haar := by
      simp only [p4Q2PZ18_originalStrippedHaarMoment, pow_one]
      rfl
    _ = (∫ X : Cfg, w X ∂haar) +
        (∫ X : Cfg, Cross X A ∂haar) := by
      simpa only [Pi.add_apply] using (integral_add hiw hic)
    _ = α := by
      rw [p4Q2IX_originalCrossingAction_HaarMean_eq_identity H A]
      rfl

/-- The ORIGINAL squared crossing Haar and the original Wilson-weighted
first crossing Haar are SU(2)-Ward invariant; hence the entire
stripped second action moment is the exact old PY6 constant theta. -/
theorem p4Q2PZ18_originalStrippedSecond_eq_theta (A : Cfg) :
    μ 2 A = θ := by
  let f : Cfg → ℝ := fun X => w X
  let g : Cfg → ℝ := fun X => Cross X A
  have hf : Continuous f := p4Q2PZ18_half_continuous H
  have hg : Continuous g := p4Q2PZ18_cross_continuous H A
  have hi1 : Integrable (fun X : Cfg => (f X)^2) haar :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun X : Cfg => 2 * (f X * g X)) haar :=
    (continuous_const.mul (hf.mul hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable (fun X : Cfg => (g X)^2) haar :=
    (hg.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd1 :
      (∫ X : Cfg, (f X)^2 + 2*(f X*g X) ∂haar) =
        (∫ X : Cfg, (f X)^2 ∂haar) +
          (∫ X : Cfg, 2*(f X*g X) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hi1 hi2)
  have hadd2 :
      (∫ X : Cfg,
          ((f X)^2 + 2*(f X*g X)) + (g X)^2 ∂haar) =
        (∫ X : Cfg, (f X)^2 + 2*(f X*g X) ∂haar) +
          (∫ X : Cfg, (g X)^2 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (hi1.add hi2) hi3)
  calc
    μ 2 A = ∫ X : Cfg,
        ((f X)^2 + 2*(f X*g X)) + (g X)^2 ∂haar := by
      unfold p4Q2PZ18_originalStrippedHaarMoment
        p4Q2PS_originalRightStrippedAction
      apply integral_congr_ae
      filter_upwards with X
      dsimp [f, g]
      ring
    _ = (∫ X : Cfg, (f X)^2 ∂haar) +
        2 * (∫ X : Cfg, f X * g X ∂haar) +
        (∫ X : Cfg, (g X)^2 ∂haar) := by
      rw [hadd2, hadd1, integral_const_mul]
    _ = θ := by
      dsimp [f, g]
      rw [p4Q2PY6_originalHalfSpatial_crossingHaar_invariant H A,
        p4Q2PY6_originalCrossingSquare_HaarMean_invariant H A]
      rfl

/-- Genuine first complete Wilson action moment has exactly the
same SU(2) Haar affine scalar alpha as the original stripped action. -/
theorem p4Q2PZ18_originalCompleteFirst_eq_halfPlusAlpha (A : Cfg) :
    M 1 A = w A + α := by
  have hiL : Integrable (fun X : Cfg => L X A) haar :=
    (p4Q2PZ18_stripped_continuous H A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    M 1 A = ∫ X : Cfg, L X A + w A ∂haar := by
      unfold p4Q2PZ16_originalLeftSlabMoment
      apply integral_congr_ae
      filter_upwards with X
      rw [p4Q2PS_originalOneSlabAction_rightSplit H X A]
      simp only [pow_one]
    _ = (∫ X : Cfg, L X A ∂haar) + w A := by
      simpa only [Pi.add_apply, integral_const] using
        (integral_add hiL (integrable_const (w A)))
    _ = w A + α := by
      rw [show (∫ X : Cfg, L X A ∂haar) = μ 1 A from by
        simp only [p4Q2PZ18_originalStrippedHaarMoment, pow_one]]
      rw [p4Q2PZ18_originalStrippedFirst_eq_alpha H A]
      ring

/-- Compact probability Haar binomial identity for the genuine
three-fold shift of any continuous real observable. -/
private theorem p4Q2PZ18_integral_shift_cube
    (f : Cfg → ℝ) (hf : Continuous f) (t : ℝ) :
    (∫ X : Cfg, (f X + t)^3 ∂haar) =
      (∫ X : Cfg, (f X)^3 ∂haar) +
      3*t*(∫ X : Cfg, (f X)^2 ∂haar) +
      3*t^2*(∫ X : Cfg, f X ∂haar) + t^3 := by
  have hi3 : Integrable (fun X : Cfg => (f X)^3) haar :=
    (hf.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun X : Cfg => (3*t)*(f X)^2) haar :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun X : Cfg => (3*t^2)*f X) haar :=
    (continuous_const.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hadd1 :
      (∫ X : Cfg, (f X)^3 + (3*t)*(f X)^2 ∂haar) =
        (∫ X : Cfg, (f X)^3 ∂haar) +
          (∫ X : Cfg, (3*t)*(f X)^2 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hi3 hi2)
  have hadd2 :
      (∫ X : Cfg, ((f X)^3 + (3*t)*(f X)^2) + (3*t^2)*f X ∂haar) =
        (∫ X : Cfg, (f X)^3 + (3*t)*(f X)^2 ∂haar) +
          (∫ X : Cfg, (3*t^2)*f X ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (hi3.add hi2) hi1)
  have hadd3 :
      (∫ X : Cfg,
          (((f X)^3 + (3*t)*(f X)^2) + (3*t^2)*f X) + t^3 ∂haar) =
        (∫ X : Cfg,
          ((f X)^3 + (3*t)*(f X)^2) + (3*t^2)*f X ∂haar) +
          (∫ X : Cfg, t^3 ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add ((hi3.add hi2).add hi1) (integrable_const (t^3)))
  calc
    (∫ X : Cfg, (f X + t)^3 ∂haar) =
      ∫ X : Cfg,
        (((f X)^3 + (3*t)*(f X)^2) + (3*t^2)*f X) + t^3 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        ring
    _ = (∫ X : Cfg, (f X)^3 ∂haar) +
      3*t*(∫ X : Cfg, (f X)^2 ∂haar) +
      3*t^2*(∫ X : Cfg, f X ∂haar) + t^3 := by
        rw [hadd3, hadd2, hadd1]
        simp only [integral_const_mul, integral_const]
        ring

/-- Haar binomial shift at degree four, valid in the actual compact
SU(2) configuration space, with no posterior factorization. -/
private theorem p4Q2PZ18_integral_shift_fourth
    (f : Cfg → ℝ) (hf : Continuous f) (t : ℝ) :
    (∫ X : Cfg, (f X + t)^4 ∂haar) =
      (∫ X : Cfg, (f X)^4 ∂haar) +
      4*t*(∫ X : Cfg, (f X)^3 ∂haar) +
      6*t^2*(∫ X : Cfg, (f X)^2 ∂haar) +
      4*t^3*(∫ X : Cfg, f X ∂haar) + t^4 := by
  have hi4 : Integrable (fun X : Cfg => (f X)^4) haar :=
    (hf.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable (fun X : Cfg => (4*t)*(f X)^3) haar :=
    (continuous_const.mul (hf.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun X : Cfg => (6*t^2)*(f X)^2) haar :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun X : Cfg => (4*t^3)*f X) haar :=
    (continuous_const.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hadd1 :
      (∫ X : Cfg, (f X)^4 + (4*t)*(f X)^3 ∂haar) =
        (∫ X : Cfg, (f X)^4 ∂haar) +
          (∫ X : Cfg, (4*t)*(f X)^3 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hi4 hi3)
  have hadd2 :
      (∫ X : Cfg,
          ((f X)^4 + (4*t)*(f X)^3) + (6*t^2)*(f X)^2 ∂haar) =
        (∫ X : Cfg, (f X)^4 + (4*t)*(f X)^3 ∂haar) +
          (∫ X : Cfg, (6*t^2)*(f X)^2 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (hi4.add hi3) hi2)
  have hadd3 :
      (∫ X : Cfg,
          (((f X)^4 + (4*t)*(f X)^3) + (6*t^2)*(f X)^2) +
            (4*t^3)*f X ∂haar) =
        (∫ X : Cfg,
          ((f X)^4 + (4*t)*(f X)^3) + (6*t^2)*(f X)^2 ∂haar) +
          (∫ X : Cfg, (4*t^3)*f X ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add ((hi4.add hi3).add hi2) hi1)
  have hadd4 :
      (∫ X : Cfg,
          ((((f X)^4 + (4*t)*(f X)^3) + (6*t^2)*(f X)^2) +
            (4*t^3)*f X) + t^4 ∂haar) =
        (∫ X : Cfg,
          (((f X)^4 + (4*t)*(f X)^3) + (6*t^2)*(f X)^2) +
            (4*t^3)*f X ∂haar) +
          (∫ X : Cfg, t^4 ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add (((hi4.add hi3).add hi2).add hi1) (integrable_const (t^4)))
  calc
    (∫ X : Cfg, (f X + t)^4 ∂haar) =
      ∫ X : Cfg,
        ((((f X)^4 + (4*t)*(f X)^3) + (6*t^2)*(f X)^2) +
          (4*t^3)*f X) + t^4 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        ring
    _ = (∫ X : Cfg, (f X)^4 ∂haar) +
      4*t*(∫ X : Cfg, (f X)^3 ∂haar) +
      6*t^2*(∫ X : Cfg, (f X)^2 ∂haar) +
      4*t^3*(∫ X : Cfg, f X ∂haar) + t^4 := by
        rw [hadd4, hadd3, hadd2, hadd1]
        simp only [integral_const_mul, integral_const]
        ring

/-- The authentic THIRD Haar moment contains only one genuinely
higher right-stripped profile: mu3 of unchanged spatial/crossing L. -/
theorem p4Q2PZ18_originalCompleteThird_strippedExpansion (A : Cfg) :
    M 3 A =
      (w A)^3 + 3*α*(w A)^2 + 3*θ*w A + μ 3 A := by
  have hshift := p4Q2PZ18_integral_shift_cube H
    (fun X : Cfg => L X A) (p4Q2PZ18_stripped_continuous H A) (w A)
  have hraw :
      M 3 A = (∫ X : Cfg, (L X A+w A)^3 ∂haar) := by
    unfold p4Q2PZ16_originalLeftSlabMoment
    apply integral_congr_ae
    filter_upwards with X
    rw [p4Q2PS_originalOneSlabAction_rightSplit H X A]
  rw [hraw, hshift]
  change μ 3 A + 3*w A*μ 2 A + 3*(w A)^2*μ 1 A + (w A)^3 = _
  rw [p4Q2PZ18_originalStrippedSecond_eq_theta H A,
    p4Q2PZ18_originalStrippedFirst_eq_alpha H A]
  ring

/-- The original FOURTH Haar moment depends on two and only two
higher genuine stripped Haar profiles, mu3 and mu4. -/
theorem p4Q2PZ18_originalCompleteFourth_strippedExpansion (A : Cfg) :
    M 4 A =
      (w A)^4 + 4*α*(w A)^3 + 6*θ*(w A)^2 +
        4*(w A)*μ 3 A + μ 4 A := by
  have hshift := p4Q2PZ18_integral_shift_fourth H
    (fun X : Cfg => L X A) (p4Q2PZ18_stripped_continuous H A) (w A)
  have hraw :
      M 4 A = (∫ X : Cfg, (L X A+w A)^4 ∂haar) := by
    unfold p4Q2PZ16_originalLeftSlabMoment
    apply integral_congr_ae
    filter_upwards with X
    rw [p4Q2PS_originalOneSlabAction_rightSplit H X A]
  rw [hraw, hshift]
  change μ 4 A + 4*w A*μ 3 A + 6*(w A)^2*μ 2 A +
    4*(w A)^3*μ 1 A + (w A)^4 = _
  rw [p4Q2PZ18_originalStrippedSecond_eq_theta H A,
    p4Q2PZ18_originalStrippedFirst_eq_alpha H A]
  ring

/-- All Haar-selected affine/quadratic and spatial-polynomial
contributions to PZ16's fourth-degree boundary kernel. -/
noncomputable def p4Q2PZ18_originalLowSpatialFourthKernel
    (A : Cfg) (t u : ℝ) : ℝ :=
  let x := w A
  (5*(x^4 + 4*α*x^3 + 6*θ*x^2) +
    10*(t+u)*(x^3 + 3*α*x^2 + 3*θ*x)) +
    10*(t^2+t*u+u^2)*(x^2+2*α*x+θ) +
    5*(t^3+t^2*u+t*u^2+u^3)*(x+α) + P4 t u

local notation "Klo" => p4Q2PZ18_originalLowSpatialFourthKernel H

/-- The ONLY extra true Haar input beyond the explicit low spatial
polynomial is the original mu3 and mu4 at the SAME middle slice A.
This is an identity, not a claim their dependence is nonzero. -/
noncomputable def p4Q2PZ18_originalHighStrippedFourthKernel
    (A : Cfg) (t u : ℝ) : ℝ :=
  5*μ 4 A + (20*w A+10*(t+u))*μ 3 A

local notation "Khi" => p4Q2PZ18_originalHighStrippedFourthKernel H

theorem p4Q2PZ18_originalConditionalTower_lowPlusHigh
    (A : Cfg) (t u : ℝ) :
    K A t u = Klo A t u + Khi A t u := by
  unfold p4Q2PZ16_originalConditionalFourthTower
    p4Q2PZ18_originalLowSpatialFourthKernel
    p4Q2PZ18_originalHighStrippedFourthKernel
  dsimp only
  rw [p4Q2PZ18_originalCompleteFourth_strippedExpansion H A,
    p4Q2PZ18_originalCompleteThird_strippedExpansion H A]
  rw [p4Q2PZ17_originalSecondMoment_quadratic H A,
    p4Q2PZ18_originalCompleteFirst_eq_halfPlusAlpha H A]
  ring

/-- Truly interacting original two-slab Haar boundary response,
with the reduced high-stripped moment sector made LITERAL.
All middle plaquettes and the complete outer Haar are unchanged. -/
noncomputable def p4Q2PZ18_originalTwoSlabLowHighBoundaryResponse
    (B C : Cfg) : ℝ :=
  ∫ A : Cfg,
    (S A B-S A C) *
      (Klo A (S A B) (S A C) + Khi A (S A B) (S A C)) ∂haar

local notation "T18" => p4Q2PZ18_originalTwoSlabLowHighBoundaryResponse H

theorem p4Q2PZ18_originalTwoSlabResponse_eq_lowPlusHigh
    (B C : Cfg) :
    p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse H B C =
      T18 B C := by
  unfold p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse
    p4Q2PZ18_originalTwoSlabLowHighBoundaryResponse
  apply integral_congr_ae
  filter_upwards with A
  rw [p4Q2PZ18_originalConditionalTower_lowPlusHigh
    H A (S A B) (S A C)]

/-- PZ18's final genuine sixth Ward expression. The independent
posterior, fake rank and a nonzero sixth witness are NOT introduced. -/
theorem p4Q2PZ18_originalSixthWard_lowHighHaar
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C -
      6*((a B-a A)*(T18 C A-J1 C A) -
         (a C-a A)*(T18 B A-J1 B A)) := by
  rw [p4Q2PZ16_originalSixthWard_conditionalMomentTower H A B C]
  rw [p4Q2PZ18_originalTwoSlabResponse_eq_lowPlusHigh H C A,
    p4Q2PZ18_originalTwoSlabResponse_eq_lowPlusHigh H B A]

end OriginalStrippedHigherHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalStrippedFirst_eq_alpha
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalStrippedSecond_eq_theta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalCompleteFirst_eq_halfPlusAlpha
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalCompleteThird_strippedExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalCompleteFourth_strippedExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalConditionalTower_lowPlusHigh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalTwoSlabResponse_eq_lowPlusHigh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ18_originalSixthWard_lowHighHaar
