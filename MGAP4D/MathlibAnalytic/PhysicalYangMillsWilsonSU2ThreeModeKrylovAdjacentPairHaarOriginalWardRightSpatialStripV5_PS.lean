import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCubicWardCrossMomentV5_PR
import Mathlib.Tactic

/-!
# P4-Q2-PS — original Wilson quartic Ward residual: strip the right spatial action

The original full one-slab Wilson action is
 S(A,B) = W(A)/2 + Cross(A,B) + W(B)/2.

Write L(A,B)=W(A)/2 + Cross(A,B), with the full intermediate
spatial Wilson action W(A)/2 still retained. Its centered
first-Haar action moment h(A)=a(A)-mean_H(a) has zero Haar mean.

PM's genuine Wilson Ward identity proves
 J(B) = integral_H S(A,B)*h(A)
is independent of B; no hypothesis is inserted.

Consequently the exact original third-order PQ residual satisfies
 R_H(B) = mean_H(c) + 3*F(B)
          + [6*J(identity)-3*mean_H(b)]*W(B)/2,
 F(B) = integral_H [L(A,B)^2*h(A) - L(A,B)*b(A)].

All potential non-affine dependence is therefore carried by F,
and the genuine fourth Wilson minor only sees F's non-affine part.
This does NOT prove F affine, F non-affine, nonzero C4 or D3>0.
The unchanged original reference Haar, full Wilson intermediate
spatial energy, Gauss-law model, and interacting physical transfer
are retained; no posterior replacement, extra axiom or sorry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonRightSpatialStrip
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H

noncomputable def p4Q2PS_originalHalfSpatialAction (A : Cfg) : ℝ :=
  (1 / 2 : ℝ) * W A

noncomputable def p4Q2PS_originalRightStrippedAction (A B : Cfg) : ℝ :=
  p4Q2PS_originalHalfSpatialAction H A + Cross A B

noncomputable def p4Q2PS_originalCenteredFirstMoment (A : Cfg) : ℝ :=
  a A - p4Q2PQ_originalFirstActionMean H

local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "L" => p4Q2PS_originalRightStrippedAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H

/-- No intermediate Wilson energy has been removed. Only the right
boundary's half-spatial Wilson term is displayed separately. -/
theorem p4Q2PS_originalOneSlabAction_rightSplit (A B : Cfg) :
    S A B = L A B + w B := by
  unfold p4Q2PS_originalRightStrippedAction
    p4Q2PS_originalHalfSpatialAction
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  ring

private theorem p4Q2PS_originalOneSlab_row_continuous (B : Cfg) :
    Continuous (fun A : Cfg => S A B) := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCont := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

private theorem p4Q2PS_originalCross_row_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Cross A B) := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCont := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

private theorem p4Q2PS_originalStripped_row_continuous (B : Cfg) :
    Continuous (fun A : Cfg => L A B) := by
  change Continuous (fun A : Cfg => (1 / 2 : ℝ) * W A + Cross A B)
  exact
    (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).add
    (p4Q2PS_originalCross_row_continuous H B)

private theorem p4Q2PS_originalFirstMoment_continuous :
    Continuous (fun A : Cfg => a A) := by
  have hEq : (fun A : Cfg => a A) =
      (fun A : Cfg => -(1 / 2 : ℝ) * W A -
        p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) := by
    funext A
    exact p4Q2PM_originalFirstMoment_spatialWilson H A
  rw [hEq]
  exact
    (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).sub
    continuous_const

private theorem p4Q2PS_integral_first_continuous (f : C(Cfg × Cfg, ℝ)) :
    Continuous (fun B : Cfg => ∫ A : Cfg, f (A, B) ∂haar) := by
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun A : Cfg => v A) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun B : Cfg => ∫ A : Cfg, f (A, B) ∂haar) =
        (fun B : Cfg => (∫ A : Cfg, v A ∂haar) B) := by
    funext B
    rw [ContinuousMap.integral_apply hv B]
    rfl
  rw [hfun]
  exact (∫ A : Cfg, v A ∂haar).continuous

private theorem p4Q2PS_originalSecondMoment_continuous :
    Continuous (fun A : Cfg => b A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 2),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 2⟩
  have hCont := p4Q2PS_integral_first_continuous H f
  change Continuous (fun A : Cfg => b A) at hCont
  exact hCont

private theorem p4Q2PS_originalCenteredFirst_continuous :
    Continuous (fun A : Cfg => h A) := by
  change Continuous (fun A : Cfg =>
    a A - p4Q2PQ_originalFirstActionMean H)
  exact (p4Q2PS_originalFirstMoment_continuous H).sub continuous_const

/-- The ORIGINAL centered first-action Haar moment integrates to zero
for every finite spatial volume, with the same normalized Haar. -/
theorem p4Q2PS_originalCenteredFirst_HaarMean_zero :
    (∫ A : Cfg, h A ∂haar) = 0 := by
  let m := p4Q2PQ_originalFirstActionMean H
  have ha : Integrable (fun A : Cfg => a A) haar :=
    (p4Q2PS_originalFirstMoment_continuous H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSubtract :
      (∫ A : Cfg, a A - m ∂haar) =
        (∫ A : Cfg, a A ∂haar) - (∫ _A : Cfg, m ∂haar) := by
    simpa only [Pi.sub_apply] using
      (integral_sub ha (integrable_const m))
  change (∫ A : Cfg, a A - m ∂haar) = 0
  rw [hSubtract]
  simp [m, p4Q2PQ_originalFirstActionMean]

/-- Genuine centered first-moment / full one-slab cross moment.
The FULL original Wilson S(A,B), including W(A)/2, is retained. -/
noncomputable def p4Q2PS_originalCenteredMixedHaar (B : Cfg) : ℝ :=
  ∫ A : Cfg, S A B * h A ∂haar

local notation "J" => p4Q2PS_originalCenteredMixedHaar H

/-- Rewrite the centered cross moment in already proved genuine
original SU(2) mixed moments; no independent Haar posterior. -/
theorem p4Q2PS_originalCenteredMixedHaar_eq (B : Cfg) :
    J B = -d B + p4Q2PQ_originalFirstActionMean H * a B := by
  let m := p4Q2PQ_originalFirstActionMean H
  have hS := p4Q2PS_originalOneSlab_row_continuous H B
  have hA := p4Q2PS_originalFirstMoment_continuous H
  have hiS : Integrable (fun A : Cfg => S A B) haar :=
    hS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiSA : Integrable (fun A : Cfg => S A B * a A) haar :=
    (hS.mul hA).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSubtract :
      (∫ A : Cfg, S A B * a A - m * S A B ∂haar) =
        (∫ A : Cfg, S A B * a A ∂haar) -
          m * (∫ A : Cfg, S A B ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hiSA (hiS.const_mul m))
  calc
    J B = (∫ A : Cfg, S A B * a A - m * S A B ∂haar) := by
      unfold p4Q2PS_originalCenteredMixedHaar
        p4Q2PS_originalCenteredFirstMoment
      apply integral_congr_ae
      filter_upwards with A
      dsimp [m]
      ring
    _ = (∫ A : Cfg, S A B * a A ∂haar) -
          m * (∫ A : Cfg, S A B ∂haar) := hSubtract
    _ = -d B + p4Q2PQ_originalFirstActionMean H * a B := by
      change (∫ A : Cfg, S A B * a A ∂haar) -
          m * (∫ A : Cfg, S A B ∂haar) =
          -(-(∫ A : Cfg, S A B * a A ∂haar)) +
          m * (-(∫ A : Cfg, S A B ∂haar))
      ring

/-- PM's exact spatial Wilson Ward identity forces the centered
cross moment J(B) to be independent of the right boundary B. -/
theorem p4Q2PS_originalCenteredMixedHaar_invariant (B : Cfg) :
    J B = J (fun _ => 1) := by
  let B₀ : Cfg := fun _ => 1
  have hB := p4Q2PS_originalCenteredMixedHaar_eq H B
  have hB₀ := p4Q2PS_originalCenteredMixedHaar_eq H B₀
  have hWard :=
    p4Q2PM_originalMixedMoment_difference_proportional H B₀ B
  change d B - d B₀ =
    p4Q2PQ_originalFirstActionMean H * (a B - a B₀) at hWard
  change J B = J B₀
  rw [hB, hB₀]
  linear_combination -hWard

/-- Remaining weighted crossing function after removing the
explicit right spatial half-action. All nonlinear Ward obstruction
is transferred to this original Haar profile. -/
noncomputable def p4Q2PS_originalStrippedWardProfile (B : Cfg) : ℝ :=
  ∫ A : Cfg,
    (L A B) ^ 2 * h A - L A B * b A ∂haar

local notation "F" => p4Q2PS_originalStrippedWardProfile H

/-- Split the full original cubic integrand into its truly stripped
part, a first centered cross moment and a zero-mean square term. -/
theorem p4Q2PS_originalWard_integrand_rightSplit (A B : Cfg) :
    (S A B) ^ 2 * h A - S A B * b A =
      ((L A B) ^ 2 * h A - L A B * b A) +
        w B * (2 * S A B * h A - b A) - (w B) ^ 2 * h A := by
  rw [p4Q2PS_originalOneSlabAction_rightSplit H A B]
  ring

/-- The exact original full-SU(2)-Wilson cubic Ward residual is
the stripped crossing profile plus a manifest affine W(B) term.
No nonzero or vanishing assumption for the stripped profile. -/
theorem p4Q2PS_originalQuarticWardResidual_rightStrip (B : Cfg) :
    p4Q2PQ_originalQuarticWardResidual H B =
      (∫ A : Cfg, c A ∂haar) +
      3 * F B +
      (6 * J (fun _ => 1) -
        3 * (∫ A : Cfg, b A ∂haar)) * w B := by
  let u : ℝ := w B
  have hS := p4Q2PS_originalOneSlab_row_continuous H B
  have hL := p4Q2PS_originalStripped_row_continuous H B
  have hH := p4Q2PS_originalCenteredFirst_continuous H
  have hB := p4Q2PS_originalSecondMoment_continuous H
  have hiS2h : Integrable (fun A : Cfg => (S A B) ^ 2 * h A) haar :=
    ((hS.pow 2).mul hH).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiSb : Integrable (fun A : Cfg => S A B * b A) haar :=
    (hS.mul hB).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiSh : Integrable (fun A : Cfg => S A B * h A) haar :=
    (hS.mul hH).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiB : Integrable (fun A : Cfg => b A) haar :=
    hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun A : Cfg => h A) haar :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiF : Integrable
      (fun A : Cfg => (L A B) ^ 2 * h A - L A B * b A) haar :=
    (((hL.pow 2).mul hH).sub (hL.mul hB)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiM : Integrable
      (fun A : Cfg => 2 * S A B * h A - b A) haar :=
    (((continuous_const.mul hS).mul hH).sub hB).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSplitSub :
      (∫ A : Cfg,
        ((L A B) ^ 2 * h A - L A B * b A) +
          u * (2 * S A B * h A - b A) -
          u ^ 2 * h A ∂haar) =
      (∫ A : Cfg,
        ((L A B) ^ 2 * h A - L A B * b A) +
          u * (2 * S A B * h A - b A) ∂haar) -
        u ^ 2 * (∫ A : Cfg, h A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub (hiF.add (hiM.const_mul u)) (hiH.const_mul (u ^ 2)))
  have hSplitAdd :
      (∫ A : Cfg,
        ((L A B) ^ 2 * h A - L A B * b A) +
          u * (2 * S A B * h A - b A) ∂haar) =
      F B + u * (∫ A : Cfg, 2 * S A B * h A - b A ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul,
      p4Q2PS_originalStrippedWardProfile] using
      (integral_add hiF (hiM.const_mul u))
  have hMIntegral :
      (∫ A : Cfg, 2 * S A B * h A - b A ∂haar) =
        2 * J B - (∫ A : Cfg, b A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul,
      p4Q2PS_originalCenteredMixedHaar] using
      (integral_sub (hiSh.const_mul 2) hiB)
  have hSIntegral :
      (∫ A : Cfg,
        (S A B) ^ 2 * h A - S A B * b A ∂haar) =
      (∫ A : Cfg, (S A B) ^ 2 * h A ∂haar) -
      (∫ A : Cfg, S A B * b A ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub hiS2h hiSb)
  have hRightIntegral :
      (∫ A : Cfg,
        (S A B) ^ 2 * h A - S A B * b A ∂haar) =
      F B + u * (2 * J (fun _ => 1) -
        (∫ A : Cfg, b A ∂haar)) := by
    calc
      (∫ A : Cfg, (S A B) ^ 2 * h A - S A B * b A ∂haar) =
          ∫ A : Cfg,
            ((L A B) ^ 2 * h A - L A B * b A) +
              u * (2 * S A B * h A - b A) -
              u ^ 2 * h A ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        exact p4Q2PS_originalWard_integrand_rightSplit H A B
      _ = F B + u * (2 * J B -
          (∫ A : Cfg, b A ∂haar)) -
          u ^ 2 * (∫ A : Cfg, h A ∂haar) := by
        rw [hSplitSub, hSplitAdd, hMIntegral]
      _ = F B + u * (2 * J (fun _ => 1) -
          (∫ A : Cfg, b A ∂haar)) := by
        rw [p4Q2PS_originalCenteredFirst_HaarMean_zero H,
          p4Q2PS_originalCenteredMixedHaar_invariant H B]
        ring
  have hPR :
      p4Q2PQ_originalQuarticWardResidual H B =
        (∫ A : Cfg, c A ∂haar) +
          3 * (∫ A : Cfg,
            (S A B) ^ 2 * h A - S A B * b A ∂haar) := by
    rw [p4Q2PR_originalQuarticWardResidual_centeredCrossMoments H B]
    rw [hSIntegral]
    ring
  rw [hRightIntegral] at hPR
  convert hPR using 1 <;> dsimp [u] <;> ring

/-- A concrete exact reduced fourth coefficient: only F's
failure to be affine in the original first Wilson action a matters.
The explicit right W(B) term cancels identically in the minor. -/
theorem p4Q2PS_originalFourthCoefficient_reducedStrippedMinor
    (A B C : Cfg) :
    2 * p4Q2PP2_originalFourthCoefficient H A B C =
      (a B - a A) * (F C - F A) -
        (a C - a A) * (F B - F A) := by
  have hA := p4Q2PS_originalQuarticWardResidual_rightStrip H A
  have hB := p4Q2PS_originalQuarticWardResidual_rightStrip H B
  have hC := p4Q2PS_originalQuarticWardResidual_rightStrip H C
  have hDet :=
    p4Q2PQ_originalFourthCoefficient_six_mul H A B C
  rw [hA, hB, hC] at hDet
  rw [p4Q2PM_originalFirstMoment_spatialWilson H A,
      p4Q2PM_originalFirstMoment_spatialWilson H B,
      p4Q2PM_originalFirstMoment_spatialWilson H C] at hDet ⊢
  unfold p4Q2PS_originalHalfSpatialAction at hDet
  linear_combination (1 / 3 : ℝ) * hDet

end OriginalWilsonRightSpatialStrip
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalOneSlabAction_rightSplit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalCenteredFirst_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalCenteredMixedHaar_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalCenteredMixedHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalWard_integrand_rightSplit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalQuarticWardResidual_rightStrip
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PS_originalFourthCoefficient_reducedStrippedMinor
