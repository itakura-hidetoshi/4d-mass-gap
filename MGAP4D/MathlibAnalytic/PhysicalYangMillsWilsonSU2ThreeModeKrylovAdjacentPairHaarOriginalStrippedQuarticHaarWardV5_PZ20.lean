import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalStrippedCubicHaarWardV5_PZ19
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUniversalFifthWardZeroV5_PY9D
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThreeCrossingWardV5_PY3C
import Mathlib.Tactic

/-!
# P4-Q2-PZ20 — original SU(2) right-stripped fourth Haar moment Ward invariance

For the UNCHANGED full finite-volume SU(2) Wilson action, write
  S(X,B) = w(X) + Cross(X,B) + w(B)
and L(X,B) = w(X) + Cross(X,B) without replacing any reference measure.

The authentic fourth right-stripped action Haar integral has five terms:
  ∫w⁴ + 4∫w³ Cross + 6∫w² Cross² + 4∫w Cross³ + ∫Cross⁴.
All five are genuinely right-boundary invariant by EXISTING Wilson Ward:
* w³*Cross: PT gauge-invariant-weight Haar Ward;
* w²*Cross²: PY7 centered-square equality, PY9D genuine centered-square
  invariance, and PY6 original complete crossing-square invariance;
* w*Cross³: PY3 exact centered triple-crossing orthogonality plus
  PZ19 full-crossing Haar left-translation;
* Cross⁴: PZ19 Haar left-translation at degree four;
* pure w⁴: manifestly independent of B.

Thus the last PZ19 higher conditional moment mu4(A) becomes the true
constant mu4(identity). PZ16's full original two-slab fourth-polarization
Haar tower has no unselected left-slab Haar boundary dependence through
degree four: it is an explicit polynomial in true intermediate
spatial Wilson w(A) with coefficients fixed by actual SU(2) Haar moments.

The outer Haar and genuine original intermediate spatial plaquettes
are NOT factored or removed, and the original one-slab response J1
is kept. No claim of W6 = 0 or W6 != 0, no physical nonzero witness,
new axiom, sorry/admit, Dobrushin or surrogate spectrum.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ20_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ20_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ20_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ20_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ20_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ20_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ20_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalStrippedQuarticWard

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "L" => p4Q2PS_originalRightStrippedAction H
local notation "μ" => p4Q2PZ18_originalStrippedHaarMoment H
local notation "M" => p4Q2PZ16_originalLeftSlabMoment H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "η3" => p4Q2PZ19_originalStrippedCubicHaarConstant H
local notation "Klo" => p4Q2PZ18_originalLowSpatialFourthKernel H
local notation "K19" => p4Q2PZ19_originalFourthSelectedCubicKernel H
local notation "T19" => p4Q2PZ19_originalTwoSlabCubicWardBoundaryResponse H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

private theorem p4Q2PZ20_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ20_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

/-- True SU(2) gauge-invariant spatial Wilson cubic weight obeys the
original one-crossing PT Haar Ward theorem at all finite even periods. -/
theorem p4Q2PZ20_originalHalfSpatialCube_crossingHaar_invariant
    (B : Cfg) :
    (∫ X : Cfg, (w X)^3 * Cross X B ∂haar) =
      (∫ X : Cfg, (w X)^3 * Cross X (fun _ => 1) ∂haar) := by
  have hc : Continuous (fun X : Cfg => (w X)^3) :=
    (p4Q2PZ20_half_continuous H).pow 3
  have hGauge (γ : Gauge) (X : Cfg) :
      w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X) = w X := by
    unfold p4Q2PS_originalHalfSpatialAction
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ X]
  have hInv : ∀ (γ : Gauge) (X : Cfg),
      (w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X))^3 = (w X)^3 := by
    intro γ X
    rw [hGauge γ X]
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant
    H (fun X : Cfg => (w X)^3) hc hInv B

/-- Reuse PY7's exact original W² crossing-square identity and
PY9D's *proved* centered square Haar Ward, not an invented
posterior independence assertion. -/
theorem p4Q2PZ20_originalHalfSpatialSquare_crossingSquareHaar_invariant
    (B : Cfg) :
    (∫ X : Cfg, (w X)^2 * (Cross X B)^2 ∂haar) =
      (∫ X : Cfg, (w X)^2 * (Cross X (fun _ => 1))^2 ∂haar) := by
  change p4Q2PY6_originalSpatialSquareTwoCrossingHaar H B =
    p4Q2PY6_originalSpatialSquareTwoCrossingHaar H (fun _ => 1)
  rw [p4Q2PY7_originalSpatialSquareCrossing_eq_centered H B,
    p4Q2PY7_originalSpatialSquareCrossing_eq_centered H (fun _ => 1),
    p4Q2PY6_originalCrossingSquare_HaarMean_invariant H B,
    p4Q2PY9_originalCenteredSquare_constant_allPeriods H B]

/-- Original SU(2) single spatial Wilson w weighted by three
complete temporal crossings is exactly its Haar spatial mean
times the independent-of-boundary crossing-cube Haar integral.
This is a consequence of PY3's proven TRUE centered orthogonality. -/
theorem p4Q2PZ20_originalHalfSpatial_crossingCube_factor
    (B : Cfg) :
    (∫ X : Cfg, w X * (Cross X B)^3 ∂haar) =
      (∫ Y : Cfg, w Y ∂haar) *
        (∫ X : Cfg, (Cross X B)^3 ∂haar) := by
  let m : ℝ := ∫ Y : Cfg, w Y ∂haar
  have hw : Continuous (fun X : Cfg => w X) :=
    p4Q2PZ20_half_continuous H
  have hc : Continuous (fun X : Cfg => Cross X B) :=
    p4Q2PZ20_cross_continuous H B
  have hh : Continuous (fun X : Cfg => h X) := by
    have heq : (fun X : Cfg => h X) =
        (fun X : Cfg => m - w X) := by
      funext X
      exact p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H X
    rw [heq]
    exact continuous_const.sub hw
  have hiM : Integrable (fun X : Cfg => m * (Cross X B)^3) haar :=
    (continuous_const.mul (hc.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun X : Cfg => (Cross X B)^3 * h X) haar :=
    ((hc.pow 3).mul hh).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : (∫ X : Cfg, (Cross X B)^3 * h X ∂haar) = 0 :=
    p4Q2PY3_originalThreeCrossingCenteredHaar_zero H B
  calc
    (∫ X : Cfg, w X * (Cross X B)^3 ∂haar) =
        ∫ X : Cfg, m * (Cross X B)^3 -
          (Cross X B)^3 * h X ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H X]
        dsimp [m]
        ring
    _ = m * (∫ X : Cfg, (Cross X B)^3 ∂haar) -
      (∫ X : Cfg, (Cross X B)^3 * h X ∂haar) := by
        simpa only [Pi.sub_apply, integral_const_mul] using
          (integral_sub hiM hiH)
    _ = (∫ Y : Cfg, w Y ∂haar) *
      (∫ X : Cfg, (Cross X B)^3 ∂haar) := by
        rw [hz]
        dsimp [m]
        ring

theorem p4Q2PZ20_originalHalfSpatial_crossingCubeHaar_invariant
    (B : Cfg) :
    (∫ X : Cfg, w X * (Cross X B)^3 ∂haar) =
      (∫ X : Cfg, w X * (Cross X (fun _ => 1))^3 ∂haar) := by
  rw [p4Q2PZ20_originalHalfSpatial_crossingCube_factor H B,
    p4Q2PZ20_originalHalfSpatial_crossingCube_factor H (fun _ => 1),
    p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 3 B]

/-- Mathlib Haar integral linearity on the exact quartic of two
continuous genuine original spatial SU(2) observables. -/
private theorem p4Q2PZ20_integral_fourth_sum
    (f g : Cfg → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ X : Cfg, (f X + g X)^4 ∂haar) =
      (∫ X : Cfg, (f X)^4 ∂haar) +
      4*(∫ X : Cfg, (f X)^3*g X ∂haar) +
      6*(∫ X : Cfg, (f X)^2*(g X)^2 ∂haar) +
      4*(∫ X : Cfg, f X*(g X)^3 ∂haar) +
      (∫ X : Cfg, (g X)^4 ∂haar) := by
  have hi4f : Integrable (fun X : Cfg => (f X)^4) haar :=
    (hf.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi3fg : Integrable (fun X : Cfg => 4*((f X)^3*g X)) haar :=
    (continuous_const.mul ((hf.pow 3).mul hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2fg2 : Integrable (fun X : Cfg => 6*((f X)^2*(g X)^2)) haar :=
    (continuous_const.mul ((hf.pow 2).mul (hg.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hifg3 : Integrable (fun X : Cfg => 4*(f X*(g X)^3)) haar :=
    (continuous_const.mul (hf.mul (hg.pow 3))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi4g : Integrable (fun X : Cfg => (g X)^4) haar :=
    (hg.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd1 :
      (∫ X : Cfg, (f X)^4 + 4*((f X)^3*g X) ∂haar) =
        (∫ X : Cfg, (f X)^4 ∂haar) +
          (∫ X : Cfg, 4*((f X)^3*g X) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hi4f hi3fg)
  have hadd2 :
      (∫ X : Cfg, ((f X)^4 + 4*((f X)^3*g X)) +
        6*((f X)^2*(g X)^2) ∂haar) =
        (∫ X : Cfg, (f X)^4 + 4*((f X)^3*g X) ∂haar) +
          (∫ X : Cfg, 6*((f X)^2*(g X)^2) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (hi4f.add hi3fg) hi2fg2)
  have hadd3 :
      (∫ X : Cfg, (((f X)^4 + 4*((f X)^3*g X)) +
        6*((f X)^2*(g X)^2)) + 4*(f X*(g X)^3) ∂haar) =
        (∫ X : Cfg, ((f X)^4 + 4*((f X)^3*g X)) +
          6*((f X)^2*(g X)^2) ∂haar) +
          (∫ X : Cfg, 4*(f X*(g X)^3) ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add ((hi4f.add hi3fg).add hi2fg2) hifg3)
  have hadd4 :
      (∫ X : Cfg, ((((f X)^4 + 4*((f X)^3*g X)) +
        6*((f X)^2*(g X)^2)) + 4*(f X*(g X)^3)) +
          (g X)^4 ∂haar) =
        (∫ X : Cfg, (((f X)^4 + 4*((f X)^3*g X)) +
          6*((f X)^2*(g X)^2)) + 4*(f X*(g X)^3) ∂haar) +
          (∫ X : Cfg, (g X)^4 ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add (((hi4f.add hi3fg).add hi2fg2).add hifg3) hi4g)
  calc
    (∫ X : Cfg, (f X + g X)^4 ∂haar) =
        ∫ X : Cfg, ((((f X)^4 + 4*((f X)^3*g X)) +
          6*((f X)^2*(g X)^2)) + 4*(f X*(g X)^3)) +
          (g X)^4 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        ring
    _ = (∫ X : Cfg, (f X)^4 ∂haar) +
      4*(∫ X : Cfg, (f X)^3*g X ∂haar) +
      6*(∫ X : Cfg, (f X)^2*(g X)^2 ∂haar) +
      4*(∫ X : Cfg, f X*(g X)^3 ∂haar) +
      (∫ X : Cfg, (g X)^4 ∂haar) := by
        rw [hadd4, hadd3, hadd2, hadd1]
        simp only [integral_const_mul]

/-- Fifth-degree Wilson-Haar structure of the true stripped fourth
moment, with no surrogate action and all four crossing sectors. -/
theorem p4Q2PZ20_originalStrippedFourth_expansion (B : Cfg) :
    μ 4 B =
      (∫ X : Cfg, (w X)^4 ∂haar) +
      4*(∫ X : Cfg, (w X)^3*Cross X B ∂haar) +
      6*(∫ X : Cfg, (w X)^2*(Cross X B)^2 ∂haar) +
      4*(∫ X : Cfg, w X*(Cross X B)^3 ∂haar) +
      (∫ X : Cfg, (Cross X B)^4 ∂haar) := by
  have hbin := p4Q2PZ20_integral_fourth_sum H
    (fun X : Cfg => w X) (fun X : Cfg => Cross X B)
    (p4Q2PZ20_half_continuous H) (p4Q2PZ20_cross_continuous H B)
  unfold p4Q2PZ18_originalStrippedHaarMoment
  simpa only [p4Q2PS_originalRightStrippedAction] using hbin

/-- TRUE fourth stripped Wilson Haar moment is boundary-independent
at all finite even periods, preserving original SU(2) interactions. -/
theorem p4Q2PZ20_originalStrippedFourthHaar_invariant (B : Cfg) :
    μ 4 B = μ 4 (fun _ => 1) := by
  rw [p4Q2PZ20_originalStrippedFourth_expansion H B,
    p4Q2PZ20_originalStrippedFourth_expansion H (fun _ => 1),
    p4Q2PZ20_originalHalfSpatialCube_crossingHaar_invariant H B,
    p4Q2PZ20_originalHalfSpatialSquare_crossingSquareHaar_invariant H B,
    p4Q2PZ20_originalHalfSpatial_crossingCubeHaar_invariant H B,
    p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 4 B]

/-- True reference Haar scalar at the original identity spatial
configuration, with all original Wilson spatial plaquettes. -/
noncomputable def p4Q2PZ20_originalStrippedFourthHaarConstant : ℝ :=
  μ 4 (fun _ => 1)

local notation "η4" => p4Q2PZ20_originalStrippedFourthHaarConstant H

theorem p4Q2PZ20_originalStrippedFourth_eq_constant (A : Cfg) :
    μ 4 A = η4 :=
  p4Q2PZ20_originalStrippedFourthHaar_invariant H A

/-- The original full fourth Wilson action moment now has an exact
monic spatial quartic law with SU(2) Haar constants only. -/
theorem p4Q2PZ20_originalCompleteFourth_quarticSpatial (A : Cfg) :
    M 4 A =
      (w A)^4 + 4*α*(w A)^3 + 6*θ*(w A)^2 +
      4*(w A)*η3 + η4 := by
  rw [p4Q2PZ19_originalCompleteFourth_quarticPlusMu4 H A,
    p4Q2PZ20_originalStrippedFourth_eq_constant H A]

/-- PZ16's entire left-Haar conditional fourth polarization kernel
is now a polynomial of the TRUE intermediate Wilson w(A) with
authentic SU(2) Haar scalars alpha, theta, eta3 and eta4. -/
noncomputable def p4Q2PZ20_originalFullySelectedFourthKernel
    (A : Cfg) (t u : ℝ) : ℝ :=
  Klo A t u + 5*η4 + (20*w A+10*(t+u))*η3

local notation "K20" => p4Q2PZ20_originalFullySelectedFourthKernel H

theorem p4Q2PZ20_originalConditionalTower_fullyHaarSelected
    (A : Cfg) (t u : ℝ) :
    p4Q2PZ16_originalConditionalFourthTower H A t u =
      K20 A t u := by
  rw [p4Q2PZ19_originalConditionalTower_cubicWardReduced H A t u]
  unfold p4Q2PZ19_originalFourthSelectedCubicKernel
    p4Q2PZ20_originalFullySelectedFourthKernel
  rw [p4Q2PZ20_originalStrippedFourth_eq_constant H A]

/-- The original complete interacting second Haar integral is
unchanged; only its genuine left conditional moment tower is selected. -/
noncomputable def p4Q2PZ20_originalTwoSlabFullySelectedHaarResponse
    (B C : Cfg) : ℝ :=
  ∫ A : Cfg, (S A B-S A C) *
    K20 A (S A B) (S A C) ∂haar

local notation "T20" => p4Q2PZ20_originalTwoSlabFullySelectedHaarResponse H

theorem p4Q2PZ20_originalTwoSlabResponse_fullyHaarSelected
    (B C : Cfg) :
    p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse H B C =
      T20 B C := by
  unfold p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse
    p4Q2PZ20_originalTwoSlabFullySelectedHaarResponse
  apply integral_congr_ae
  filter_upwards with A
  rw [p4Q2PZ20_originalConditionalTower_fullyHaarSelected
    H A (S A B) (S A C)]

/-- The true original sixth Ward obstruction with all left-slab
Haar moments through degree four reduced to explicit Wilson
spatial polynomials; no zero/nonzero conclusion is presumed. -/
theorem p4Q2PZ20_originalSixthWard_fullyHaarSelected
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C -
      6*((a B-a A)*(T20 C A-J1 C A) -
         (a C-a A)*(T20 B A-J1 B A)) := by
  rw [p4Q2PZ16_originalSixthWard_conditionalMomentTower H A B C]
  rw [p4Q2PZ20_originalTwoSlabResponse_fullyHaarSelected H C A,
    p4Q2PZ20_originalTwoSlabResponse_fullyHaarSelected H B A]

end OriginalStrippedQuarticWard
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalHalfSpatialCube_crossingHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalHalfSpatialSquare_crossingSquareHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalHalfSpatial_crossingCube_factor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalHalfSpatial_crossingCubeHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalStrippedFourth_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalStrippedFourthHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalStrippedFourth_eq_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalCompleteFourth_quarticSpatial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalConditionalTower_fullyHaarSelected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalTwoSlabResponse_fullyHaarSelected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ20_originalSixthWard_fullyHaarSelected
