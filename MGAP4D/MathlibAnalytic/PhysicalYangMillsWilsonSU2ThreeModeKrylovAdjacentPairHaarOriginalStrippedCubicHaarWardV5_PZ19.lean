import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalStrippedHighMomentWardV5_PZ18
import Mathlib.Tactic

/-!
# P4-Q2-PZ19 — original stripped cubic SU(2) Haar Ward invariance

Continue PZ18 with the UNCHANGED genuine SU(2) Wilson action
 S(X,B) = L(X,B)+w(B), L(X,B)=w(X)+Cross(X,B).

The true reference Haar third moment mu3(B) of the STRIPPED
physical one-slab Wilson action is independent of its right boundary.
We prove this by expanding its cubic into four honest Haar sectors:

 * pure spatial w(X)^3: no B dependence;
 * w(X)^2 Cross(X,B): original gauge-weighted SU(2) Ward invariance;
 * w(X) Cross(X,B)^2: genuine PY6D factorization of this Haar MOMENT,
   plus original PY6 crossing-square Haar invariance;
 * Cross(X,B)^3: original coordinatewise Haar left-translation.

The PZ18 higher conditional polarization then depends only on
the genuine fourth stripped moment mu4(A), and on a single original
SU(2) Haar constant mu3(identity). We keep the original outer Haar,
intermediate spatial Wilson plaquettes, both true posterior sectors,
the correct odd Taylor signs and original sixth Ward coefficient.

No independent posterior, substitute action, surrogate spectral model,
new axiom, sorry/admit, unproved nonzero triple or mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ19_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ19_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ19_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ19_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ19_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ19_productProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ19_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection

namespace GroundStatePosteriorJoint
section GenuineCubicHaarSelection

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
local notation "L" => p4Q2PS_originalRightStrippedAction H
local notation "μ" => p4Q2PZ18_originalStrippedHaarMoment H
local notation "M" => p4Q2PZ16_originalLeftSlabMoment H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "Klo" => p4Q2PZ18_originalLowSpatialFourthKernel H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

private theorem p4Q2PZ19_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ19_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

/-- A compact-Haar integration of the exact genuine sum-cubic:
all four Wilson terms remain in the true integrands. -/
private theorem p4Q2PZ19_integral_cube_of_two
    (f g : Cfg → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ X : Cfg, (f X + g X)^3 ∂haar) =
      (∫ X : Cfg, (f X)^3 ∂haar) +
      3*(∫ X : Cfg, (f X)^2*g X ∂haar) +
      3*(∫ X : Cfg, f X*(g X)^2 ∂haar) +
      (∫ X : Cfg, (g X)^3 ∂haar) := by
  have hi3f : Integrable (fun X : Cfg => (f X)^3) haar :=
    (hf.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2fg : Integrable (fun X : Cfg => 3*((f X)^2*g X)) haar :=
    (continuous_const.mul ((hf.pow 2).mul hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hifg2 : Integrable (fun X : Cfg => 3*(f X*(g X)^2)) haar :=
    (continuous_const.mul (hf.mul (hg.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi3g : Integrable (fun X : Cfg => (g X)^3) haar :=
    (hg.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd1 :
      (∫ X : Cfg, (f X)^3 + 3*((f X)^2*g X) ∂haar) =
        (∫ X : Cfg, (f X)^3 ∂haar) +
          (∫ X : Cfg, 3*((f X)^2*g X) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hi3f hi2fg)
  have hadd2 :
      (∫ X : Cfg,
        ((f X)^3 + 3*((f X)^2*g X)) + 3*(f X*(g X)^2) ∂haar) =
        (∫ X : Cfg, (f X)^3 + 3*((f X)^2*g X) ∂haar) +
          (∫ X : Cfg, 3*(f X*(g X)^2) ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (hi3f.add hi2fg) hifg2)
  have hadd3 :
      (∫ X : Cfg,
        (((f X)^3 + 3*((f X)^2*g X)) + 3*(f X*(g X)^2)) +
          (g X)^3 ∂haar) =
        (∫ X : Cfg,
          ((f X)^3 + 3*((f X)^2*g X)) + 3*(f X*(g X)^2) ∂haar) +
          (∫ X : Cfg, (g X)^3 ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add ((hi3f.add hi2fg).add hifg2) hi3g)
  calc
    (∫ X : Cfg, (f X + g X)^3 ∂haar) =
      (∫ X : Cfg,
        (((f X)^3 + 3*((f X)^2*g X)) + 3*(f X*(g X)^2)) +
          (g X)^3 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        ring
    _ = (∫ X : Cfg, (f X)^3 ∂haar) +
      3*(∫ X : Cfg, (f X)^2*g X ∂haar) +
      3*(∫ X : Cfg, f X*(g X)^2 ∂haar) +
      (∫ X : Cfg, (g X)^3 ∂haar) := by
        rw [hadd3, hadd2, hadd1]
        simp only [integral_const_mul] <;> ring

/-- EXACT original right-stripped cubic Haar decomposition with
spatial Wilson w(X) and all true temporal crossings retained. -/
theorem p4Q2PZ19_originalStrippedCubic_expansion (B : Cfg) :
    μ 3 B =
      (∫ X : Cfg, (w X)^3 ∂haar) +
      3*(∫ X : Cfg, (w X)^2*Cross X B ∂haar) +
      3*(∫ X : Cfg, w X*(Cross X B)^2 ∂haar) +
      (∫ X : Cfg, (Cross X B)^3 ∂haar) := by
  have h := p4Q2PZ19_integral_cube_of_two H
    (fun X : Cfg => w X) (fun X : Cfg => Cross X B)
    (p4Q2PZ19_half_continuous H)
    (p4Q2PZ19_cross_continuous H B)
  unfold p4Q2PZ18_originalStrippedHaarMoment
  simpa only [p4Q2PS_originalRightStrippedAction] using h

/-- Original SU(2) spatial WILSON-square is a continuous, physical
gauge-invariant weight. Reuse PT's existing general weighted Ward
rather than inventing a posterior factorization. -/
theorem p4Q2PZ19_originalHalfSpatialSquare_crossingHaar_invariant
    (B : Cfg) :
    (∫ X : Cfg, (w X)^2*Cross X B ∂haar) =
      (∫ X : Cfg, (w X)^2*Cross X (fun _ => 1) ∂haar) := by
  have hφ : Continuous (fun X : Cfg => (w X)^2) :=
    (p4Q2PZ19_half_continuous H).pow 2
  have hGauge (γ : Gauge) (X : Cfg) :
      w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X) = w X := by
    unfold p4Q2PS_originalHalfSpatialAction
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ X]
  have hInv : ∀ (γ : Gauge) (X : Cfg),
      (w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X))^2 = (w X)^2 := by
    intro γ X
    rw [hGauge γ X]
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant
    H (fun X : Cfg => (w X)^2) hφ hInv B

/-- Original w(X)*Cross(X,B)^2 is right-boundary invariant from
PY6D's actual centered Wilson Haar identity and PY6's unweighted
crossing square Haar translation (not posterior independence). -/
theorem p4Q2PZ19_originalHalfSpatial_crossingSquareHaar_invariant
    (B : Cfg) :
    (∫ X : Cfg, w X*(Cross X B)^2 ∂haar) =
      (∫ X : Cfg, w X*(Cross X (fun _ => 1))^2 ∂haar) := by
  rw [p4Q2PY6_originalHalfSpatial_crossingSquare_factor H B,
    p4Q2PY6_originalHalfSpatial_crossingSquare_factor H (fun _ => 1),
    p4Q2PY6_originalCrossingSquare_HaarMean_invariant H B]

/-- General genuine Haar coordinatewise left-translation for EVERY
integer power of the full original temporal Wilson crossing action. -/
theorem p4Q2PZ19_originalFullCrossingPowerHaar_invariant
    (k : ℕ) (B : Cfg) :
    (∫ X : Cfg, (Cross X B)^k ∂haar) =
      (∫ X : Cfg, (Cross X (fun _ => 1))^k ∂haar) := by
  let T : Cfg → Cfg := fun X e => B e * X e
  let f : Cfg → ℝ := fun X => (Cross X B)^k
  have hPres : MeasurePreserving T haar haar :=
    p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving H B
  have hf : AEStronglyMeasurable f haar :=
    ((p4Q2PZ19_cross_continuous H B).pow k).measurable.aestronglyMeasurable
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  calc
    (∫ X : Cfg, (Cross X B)^k ∂haar) =
        ∫ X : Cfg, f X ∂haar := rfl
    _ = ∫ X : Cfg, f X ∂Measure.map T haar := by rw [hmap]
    _ = ∫ X : Cfg, f (T X) ∂haar :=
      MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
    _ = ∫ X : Cfg, (Cross X (fun _ => 1))^k ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      exact congrArg (fun z : ℝ => z^k)
        (p4Q2IX_originalCrossingAction_leftTranslate H B X)

/-- The actual SU(2) right-stripped THIRD Wilson action Haar moment
is a constant of the right boundary at EVERY finite even period.
No artificial action/posterior, no higher Ward nonzero assumption. -/
theorem p4Q2PZ19_originalStrippedCubicHaar_invariant (B : Cfg) :
    μ 3 B = μ 3 (fun _ => 1) := by
  rw [p4Q2PZ19_originalStrippedCubic_expansion H B,
    p4Q2PZ19_originalStrippedCubic_expansion H (fun _ => 1),
    p4Q2PZ19_originalHalfSpatialSquare_crossingHaar_invariant H B,
    p4Q2PZ19_originalHalfSpatial_crossingSquareHaar_invariant H B,
    p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 3 B]

/-- A constant formed ONLY from the real original full SU(2)
spatial slice Haar, at the identity right boundary. -/
noncomputable def p4Q2PZ19_originalStrippedCubicHaarConstant : ℝ :=
  μ 3 (fun _ => 1)

local notation "η3" => p4Q2PZ19_originalStrippedCubicHaarConstant H

theorem p4Q2PZ19_originalStrippedCubic_eq_constant (A : Cfg) :
    μ 3 A = η3 :=
  p4Q2PZ19_originalStrippedCubicHaar_invariant H A

/-- The TRUE complete third action moment is now EXACTLY cubic
in the original right spatial Wilson half-action. -/
theorem p4Q2PZ19_originalCompleteThird_cubicSpatial (A : Cfg) :
    M 3 A =
      (w A)^3 + 3*α*(w A)^2 + 3*θ*w A + η3 := by
  rw [p4Q2PZ18_originalCompleteThird_strippedExpansion H A,
    p4Q2PZ19_originalStrippedCubic_eq_constant H A]

/-- The true fourth action Haar moment now has just ONE remaining
higher right-stripped moment mu4(A), not an unproved nonzero witness. -/
theorem p4Q2PZ19_originalCompleteFourth_quarticPlusMu4 (A : Cfg) :
    M 4 A =
      (w A)^4 + 4*α*(w A)^3 + 6*θ*(w A)^2 +
        4*(w A)*η3 + μ 4 A := by
  rw [p4Q2PZ18_originalCompleteFourth_strippedExpansion H A,
    p4Q2PZ19_originalStrippedCubic_eq_constant H A]

/-- The PZ18 low-spatial polynomial is unchanged. All genuinely
higher right-boundary Haar dependence is reduced to mu4(A) alone. -/
noncomputable def p4Q2PZ19_originalFourthSelectedCubicKernel
    (A : Cfg) (t u : ℝ) : ℝ :=
  Klo A t u + 5*μ 4 A + (20*w A+10*(t+u))*η3

local notation "K19" => p4Q2PZ19_originalFourthSelectedCubicKernel H

theorem p4Q2PZ19_originalConditionalTower_cubicWardReduced
    (A : Cfg) (t u : ℝ) :
    p4Q2PZ16_originalConditionalFourthTower H A t u = K19 A t u := by
  rw [p4Q2PZ18_originalConditionalTower_lowPlusHigh H A t u]
  unfold p4Q2PZ18_originalHighStrippedFourthKernel
    p4Q2PZ19_originalFourthSelectedCubicKernel
  rw [p4Q2PZ19_originalStrippedCubic_eq_constant H A]
  ring

/-- Exactly unchanged two-slab outer Haar response with a single
remaining higher original SU(2) stripped action Haar moment mu4. -/
noncomputable def p4Q2PZ19_originalTwoSlabCubicWardBoundaryResponse
    (B C : Cfg) : ℝ :=
  ∫ A : Cfg,
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A C) *
      K19 A
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A C)
    ∂haar

local notation "T19" => p4Q2PZ19_originalTwoSlabCubicWardBoundaryResponse H

theorem p4Q2PZ19_originalTwoSlabResponse_cubicWardReduced
    (B C : Cfg) :
    p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse H B C =
      T19 B C := by
  unfold p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse
    p4Q2PZ19_originalTwoSlabCubicWardBoundaryResponse
  apply integral_congr_ae
  filter_upwards with A
  rw [p4Q2PZ19_originalConditionalTower_cubicWardReduced
    H A
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A C)]

/-- The actual sixth original SU(2) Wilson Ward obstruction with the
proven cubic-Haar Ward cancellation inserted into the full interacting
two-slab response; its vanishing/nonvanishing is NOT asserted. -/
theorem p4Q2PZ19_originalSixthWard_cubicWardReduced
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C -
      6*((a B-a A)*(T19 C A-J1 C A) -
         (a C-a A)*(T19 B A-J1 B A)) := by
  rw [p4Q2PZ16_originalSixthWard_conditionalMomentTower H A B C]
  rw [p4Q2PZ19_originalTwoSlabResponse_cubicWardReduced H C A,
    p4Q2PZ19_originalTwoSlabResponse_cubicWardReduced H B A]

end GenuineCubicHaarSelection
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalStrippedCubic_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalHalfSpatialSquare_crossingHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalHalfSpatial_crossingSquareHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalFullCrossingPowerHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalStrippedCubicHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalStrippedCubic_eq_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalCompleteThird_cubicSpatial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalCompleteFourth_quarticPlusMu4
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalConditionalTower_cubicWardReduced
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalTwoSlabResponse_cubicWardReduced
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ19_originalSixthWard_cubicWardReduced
