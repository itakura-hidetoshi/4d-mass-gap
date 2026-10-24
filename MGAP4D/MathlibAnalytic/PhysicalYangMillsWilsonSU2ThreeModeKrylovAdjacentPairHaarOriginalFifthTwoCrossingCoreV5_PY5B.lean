import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthSingleCrossingWardV5_PY5
import Mathlib.Tactic

/-!
# P4-Q2-PY5B — genuine fifth Ward residual: only one weighted TWO-crossing profile

For the original full SU(2) Wilson action, write
  S(A,B)=w(A)+w(B)+Cross(A,B),
  h(A)=a(A)-mean(a),  k(A)=2w(A)h(A)-b(A),
  f5(A)=c(A)-3w(A)b(A)+3w(A)^2 h(A).

PY3 eliminates the TRUE centered Cross^3 term and PW3 eliminates
the centered Cross^2 term. Exact pointwise expansion of PY4's complete
fifth Ward Haar residual then gives

  R5(B) = mean(u) + P_spatial(B)
          -4 ∫f5(A) Cross(A,I)
          -12 w(B) ∫k(A) Cross(A,I)
          -12 w(B)^2 ∫h(A) Cross(A,I)
          -6 ∫k(A) Cross(A,B)^2
          -2 s_H b(B).

PY5's gauge Ward identities make every SINGLE-crossing integral above
right-boundary independent. Thus genuine crossing-dependent
nonpolynomial behavior is confined to the unchanged two-crossing
weight k(A), with full spatial plaquette Wilson action retained.
No independence of original interacting posteriors, artificial spectral
measure, nonzero fifth coefficient/rank claim, new axiom, sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY5B_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY5B_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY5B_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY5B_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY5B_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section GenuineFifthTwoCrossingCore
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "k" => p4Q2PT_originalSingleCrossingWardWeight H
local notation "f5" => p4Q2PY5_originalHigherSingleCrossingWardWeight H
local notation "s" => p4Q2PY_originalQuarticWardSlope H
local notation "R5" => p4Q2PY_originalFifthWardResidual H

/-- The zero-crossing fifth-order Haar sector: a polynomial of the
UNMODIFIED right half-spatial Wilson action w(B), with coefficients
that are real original spatial Haar action moments. -/
noncomputable def p4Q2PY5_originalPureSpatialFifthProfile (B : Cfg) : ℝ :=
  ∫ A : Cfg,
    -4 * (w A + w B) * c A +
      6 * (w A + w B) ^ 2 * b A -
        4 * (w A + w B) ^ 3 * h A ∂haar

/-- The sole possible explicitly non-polynomial crossing-dependent
part remaining after gauge/center Ward reductions. No assertion that
this original two-crossing Haar profile is zero or non-affine. -/
noncomputable def p4Q2PY5_originalWeightedTwoCrossingHaar (B : Cfg) : ℝ :=
  ∫ A : Cfg, k A * (Cross A B) ^ 2 ∂haar

local notation "P" => p4Q2PY5_originalPureSpatialFifthProfile H
local notation "V2" => p4Q2PY5_originalWeightedTwoCrossingHaar H

/-- Exact fifth Ward reduction in the ORIGINAL fully interacting
SU(2) Wilson theory: single-crossing terms are boundary-constant,
the triple-crossing term and centered two-crossing term are genuinely
zero, leaving just the k-weighted original two-crossing profile. -/
theorem p4Q2PY5_originalFifthWardResidual_twoCrossingReduced
    (B : Cfg) :
    R5 B =
      (∫ A : Cfg, u A ∂haar) + P B -
      4 * (∫ A : Cfg, f5 A * Cross A (fun _ => 1) ∂haar) -
      12 * w B *
        (∫ A : Cfg, k A * Cross A (fun _ => 1) ∂haar) -
      12 * (w B) ^ 2 *
        (∫ A : Cfg, h A * Cross A (fun _ => 1) ∂haar) -
      6 * V2 B - 2 * s * b B := by
  let z : Cfg → ℝ := fun A => w A + w B
  let p : Cfg → ℝ := fun A =>
    -4 * z A * c A + 6 * (z A) ^ 2 * b A - 4 * (z A) ^ 3 * h A
  let x0 : Cfg → ℝ := fun A => f5 A * Cross A B
  let x1 : Cfg → ℝ := fun A => k A * Cross A B
  let x2 : Cfg → ℝ := fun A => h A * Cross A B
  let x3 : Cfg → ℝ := fun A => k A * (Cross A B) ^ 2
  let x4 : Cfg → ℝ := fun A => (Cross A B) ^ 2 * h A
  let poly : Cfg → ℝ := fun A =>
    ((z A) ^ 3 + 3 * (z A) ^ 2 * Cross A B +
      3 * z A * (Cross A B) ^ 2) * h A
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hz : Continuous z := hw.add continuous_const
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hS : Continuous (fun A : Cfg => S A B) := by
    have hc := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have ha : Continuous (fun A : Cfg => a A) := by
    have heq : (fun A : Cfg => a A) =
        fun A : Cfg => -(1 / 2 : ℝ) * W A -
          p4Q2JE_originalWilsonHaarZeroDerivativeConstant H := by
      funext A
      exact p4Q2PM_originalFirstMoment_spatialWilson H A
    rw [heq]
    exact (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous
        H 2)).sub continuous_const
  have hh : Continuous (fun A : Cfg => h A) := by
    change Continuous (fun A : Cfg =>
      a A - p4Q2PQ_originalFirstActionMean H)
    exact ha.sub continuous_const
  have hb := p4Q2PT_originalSecondMoment_continuous H
  have hc := p4Q2PY5_originalThirdMoment_continuous H
  have hk := p4Q2PT_originalSingleCrossingWardWeight_continuous H
  have hf5 := p4Q2PY5_originalHigherSingleCrossingWardWeight_continuous H
  have hp : Continuous p := by
    dsimp [p]
    exact
      (((continuous_const.mul hz).mul hc).add
        ((continuous_const.mul (hz.pow 2)).mul hb)).sub
        ((continuous_const.mul (hz.pow 3)).mul hh)
  have h0 : Continuous x0 := hf5.mul hCross
  have h1 : Continuous x1 := hk.mul hCross
  have h2 : Continuous x2 := hh.mul hCross
  have h3 : Continuous x3 := hk.mul (hCross.pow 2)
  have h4 : Continuous x4 := (hCross.pow 2).mul hh
  have hPoly : Continuous poly := by
    dsimp [poly]
    exact
      (((hz.pow 3).add
        ((continuous_const.mul (hz.pow 2)).mul hCross)).add
        ((continuous_const.mul hz).mul (hCross.pow 2))).mul hh
  have hSC : Integrable (fun A : Cfg => S A B * c A) haar :=
    (hS.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS2b : Integrable (fun A : Cfg => (S A B)^2 * b A) haar :=
    ((hS.pow 2).mul hb).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPolInt : Integrable poly haar :=
    hPoly.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP : Integrable p haar :=
    hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi0 : Integrable x0 haar :=
    h0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable x1 haar :=
    h1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable x2 haar :=
    h2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable x3 haar :=
    h3.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi4 : Integrable x4 haar :=
    h4.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hOriginalIntegral :
      (∫ A : Cfg, -4 * (S A B * c A) +
        6 * ((S A B)^2 * b A) - 4 * poly A ∂haar) =
      -4 * (∫ A : Cfg, S A B * c A ∂haar) +
        6 * (∫ A : Cfg, (S A B)^2 * b A ∂haar) -
        4 * (∫ A : Cfg, poly A ∂haar) := by
    have hAdd :
        (∫ A : Cfg, -4 * (S A B * c A) +
          6 * ((S A B)^2 * b A) ∂haar) =
        (∫ A : Cfg, -4 * (S A B * c A) ∂haar) +
          (∫ A : Cfg, 6 * ((S A B)^2 * b A) ∂haar) := by
      simpa only [Pi.add_apply] using
        (integral_add (hSC.const_mul (-4)) (hS2b.const_mul 6))
    have hSub :
        (∫ A : Cfg, -4 * (S A B * c A) +
          6 * ((S A B)^2 * b A) - 4 * poly A ∂haar) =
        (∫ A : Cfg, -4 * (S A B * c A) +
          6 * ((S A B)^2 * b A) ∂haar) -
          (∫ A : Cfg, 4 * poly A ∂haar) := by
      simpa only [Pi.sub_apply] using
        (integral_sub ((hSC.const_mul (-4)).add (hS2b.const_mul 6))
          (hPolInt.const_mul 4))
    rw [hSub, hAdd]
    simp only [integral_const_mul]
  have hPoint (A : Cfg) :
      -4 * (S A B * c A) + 6 * ((S A B)^2 * b A) -
        4 * poly A =
      ((((p A - 4 * x0 A) - 12 * w B * x1 A) -
        12 * (w B)^2 * x2 A) - 6 * x3 A) -
        12 * w B * x4 A := by
    rw [p4Q2PS_originalOneSlabAction_rightSplit H A B]
    dsimp [z, p, poly, x0, x1, x2, x3, x4]
    unfold p4Q2PS_originalRightStrippedAction
      p4Q2PY5_originalHigherSingleCrossingWardWeight
      p4Q2PT_originalSingleCrossingWardWeight
    ring
  have hiA : Integrable (fun A : Cfg => p A - 4 * x0 A) haar :=
    hP.sub (hi0.const_mul 4)
  have hiB : Integrable (fun A : Cfg =>
      (p A - 4 * x0 A) - 12 * w B * x1 A) haar :=
    hiA.sub (hi1.const_mul (12 * w B))
  have hiC : Integrable (fun A : Cfg =>
      ((p A - 4 * x0 A) - 12 * w B * x1 A) -
        12 * (w B)^2 * x2 A) haar :=
    hiB.sub (hi2.const_mul (12 * (w B)^2))
  have hiD : Integrable (fun A : Cfg =>
      (((p A - 4 * x0 A) - 12 * w B * x1 A) -
        12 * (w B)^2 * x2 A) - 6 * x3 A) haar :=
    hiC.sub (hi3.const_mul 6)
  have hStep0 :
      (∫ A : Cfg, p A - 4 * x0 A ∂haar) =
      (∫ A : Cfg, p A ∂haar) -
        4 * (∫ A : Cfg, x0 A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hP (hi0.const_mul 4))
  have hStep1 :
      (∫ A : Cfg, (p A - 4 * x0 A) - 12 * w B * x1 A ∂haar) =
      (∫ A : Cfg, p A - 4 * x0 A ∂haar) -
        12 * w B * (∫ A : Cfg, x1 A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hiA (hi1.const_mul (12 * w B)))
  have hStep2 :
      (∫ A : Cfg,
        ((p A - 4 * x0 A) - 12 * w B * x1 A) -
          12 * (w B)^2 * x2 A ∂haar) =
      (∫ A : Cfg, (p A - 4 * x0 A) - 12 * w B * x1 A ∂haar) -
        12 * (w B)^2 * (∫ A : Cfg, x2 A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hiB (hi2.const_mul (12 * (w B)^2)))
  have hStep3 :
      (∫ A : Cfg,
        (((p A - 4 * x0 A) - 12 * w B * x1 A) -
          12 * (w B)^2 * x2 A) - 6 * x3 A ∂haar) =
      (∫ A : Cfg,
        ((p A - 4 * x0 A) - 12 * w B * x1 A) -
          12 * (w B)^2 * x2 A ∂haar) -
        6 * (∫ A : Cfg, x3 A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hiC (hi3.const_mul 6))
  have hStep4 :
      (∫ A : Cfg,
        ((((p A - 4 * x0 A) - 12 * w B * x1 A) -
          12 * (w B)^2 * x2 A) - 6 * x3 A) -
          12 * w B * x4 A ∂haar) =
      (∫ A : Cfg,
        (((p A - 4 * x0 A) - 12 * w B * x1 A) -
          12 * (w B)^2 * x2 A) - 6 * x3 A ∂haar) -
        12 * w B * (∫ A : Cfg, x4 A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hiD (hi4.const_mul (12 * w B)))
  have hExpandIntegral :
      (∫ A : Cfg,
        ((((p A - 4 * x0 A) - 12 * w B * x1 A) -
          12 * (w B)^2 * x2 A) - 6 * x3 A) -
          12 * w B * x4 A ∂haar) =
      (∫ A : Cfg, p A ∂haar) -
        4 * (∫ A : Cfg, x0 A ∂haar) -
        12 * w B * (∫ A : Cfg, x1 A ∂haar) -
        12 * (w B)^2 * (∫ A : Cfg, x2 A ∂haar) -
        6 * (∫ A : Cfg, x3 A ∂haar) -
        12 * w B * (∫ A : Cfg, x4 A ∂haar) := by
    rw [hStep4, hStep3, hStep2, hStep1, hStep0]
  have hCollapse :
      (∫ A : Cfg, -4 * (S A B * c A) +
        6 * ((S A B)^2 * b A) - 4 * poly A ∂haar) =
      (∫ A : Cfg, p A ∂haar) -
        4 * (∫ A : Cfg, x0 A ∂haar) -
        12 * w B * (∫ A : Cfg, x1 A ∂haar) -
        12 * (w B)^2 * (∫ A : Cfg, x2 A ∂haar) -
        6 * (∫ A : Cfg, x3 A ∂haar) -
        12 * w B * (∫ A : Cfg, x4 A ∂haar) := by
    calc
      (∫ A : Cfg, -4 * (S A B * c A) +
        6 * ((S A B)^2 * b A) - 4 * poly A ∂haar) =
          ∫ A : Cfg,
            ((((p A - 4 * x0 A) - 12 * w B * x1 A) -
              12 * (w B)^2 * x2 A) - 6 * x3 A) -
              12 * w B * x4 A ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        exact hPoint A
      _ = _ := hExpandIntegral
  have hZero : (∫ A : Cfg, x4 A ∂haar) = 0 :=
    p4Q2PW3_originalTwoCrossingCenteredHaar_zero H B
  have hx0 :
      (∫ A : Cfg, x0 A ∂haar) =
      (∫ A : Cfg, f5 A * Cross A (fun _ => 1) ∂haar) :=
    p4Q2PY5_originalHigherSingleCrossingWardHaar_invariant H B
  have hx1 :
      (∫ A : Cfg, x1 A ∂haar) =
      (∫ A : Cfg, k A * Cross A (fun _ => 1) ∂haar) :=
    p4Q2PT_originalSingleCrossingWardHaar_invariant H B
  have hx2 :
      (∫ A : Cfg, x2 A ∂haar) =
      (∫ A : Cfg, h A * Cross A (fun _ => 1) ∂haar) :=
    p4Q2PY5_originalCenteredFirst_singleCrossingHaar_invariant H B
  have hR :=
    p4Q2PY4_originalFifthWardResidual_noPureThreeCrossing H B
  change R5 B =
      (∫ A : Cfg, u A ∂haar) -
      4 * (∫ A : Cfg, S A B * c A ∂haar) +
      6 * (∫ A : Cfg, (S A B)^2 * b A ∂haar) -
      4 * (∫ A : Cfg, poly A ∂haar) -
      2 * s * b B at hR
  have hR' :
      R5 B = (∫ A : Cfg, u A ∂haar) +
        (∫ A : Cfg,
          -4 * (S A B * c A) +
            6 * ((S A B)^2 * b A) - 4 * poly A ∂haar) -
        2 * s * b B := by
    rw [hOriginalIntegral]
    linear_combination hR
  rw [hCollapse, hx0, hx1, hx2, hZero] at hR'
  change
    R5 B = (∫ A : Cfg, u A ∂haar) +
      (∫ A : Cfg, p A ∂haar) -
      4 * (∫ A : Cfg, f5 A * Cross A (fun _ => 1) ∂haar) -
      12 * w B * (∫ A : Cfg, k A * Cross A (fun _ => 1) ∂haar) -
      12 * (w B)^2 * (∫ A : Cfg, h A * Cross A (fun _ => 1) ∂haar) -
      6 * (∫ A : Cfg, x3 A ∂haar) -
      2 * s * b B
  convert hR' using 1; ring

end GenuineFifthTwoCrossingCore
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalFifthWardResidual_twoCrossingReduced
