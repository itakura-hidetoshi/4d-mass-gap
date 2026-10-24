import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalQuarticActionHaarSplitV5_PY4
import Mathlib.Tactic

/-!
# P4-Q2-PY4B — authentic outer Haar split and centered fifth Ward residual

PY4 gives the true complete two-slab Wilson inner quartic Haar identity.
Integrate that identity over the ORIGINAL intermediate SU(2) Haar,
without factoring physical interacting posteriors. Then subtract u(B)
and the exact fifth Ward counterterms of PY2.

The fifth Ward residual becomes
 R5(B)=mean_H(u)-4∫ S(A,B)c(A) dμ(A)
     +6∫ S(A,B)^2 b(A) dμ(A)
     -4∫ S(A,B)^3 h(A) dμ(A)-2s_H b(B),
 h=a-mean_H(a).
Thus the cubic centered-crossing sector is isolated for PY3's genuine
three-crossing vanishing theorem. No nonzero/zero fifth coefficient,
spectral substitute, Dobrushin, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY4B_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY4B_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY4B_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY4B_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY4B_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalFifthWardHaarResidualSplit
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H
local notation "m" => p4Q2PQ_originalFirstActionMean H
local notation "s" => p4Q2PY_originalQuarticWardSlope H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "R5" => p4Q2PY_originalFifthWardResidual H

private theorem p4Q2PY4B_oneSlabAction_row_continuous (B : Cfg) :
    Continuous (fun A : Cfg => S A B) := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hc

private theorem p4Q2PY4B_integral_first_continuous
    (f : C(Cfg × Cfg, ℝ)) :
    Continuous (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) := by
  let q : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hq : Integrable (fun X : Cfg => q X) haar :=
    q.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) =
        (fun A : Cfg => (∫ X : Cfg, q X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hq A]
    rfl
  rw [hfun]
  exact (∫ X : Cfg, q X ∂haar).continuous

private theorem p4Q2PY4B_firstMoment_continuous :
    Continuous (fun A : Cfg => a A) := by
  have hEq : (fun A : Cfg => a A) =
      fun A : Cfg => -(1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A -
          p4Q2JE_originalWilsonHaarZeroDerivativeConstant H := by
    funext A
    exact p4Q2PM_originalFirstMoment_spatialWilson H A
  rw [hEq]
  exact (continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).sub
      continuous_const

private theorem p4Q2PY4B_secondMoment_continuous :
    Continuous (fun A : Cfg => b A) :=
  p4Q2PT_originalSecondMoment_continuous H

private theorem p4Q2PY4B_thirdMoment_continuous :
    Continuous (fun A : Cfg => c A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 3),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 3⟩
  have hc := (p4Q2PY4B_integral_first_continuous H f).neg
  change Continuous (fun A : Cfg => c A) at hc
  exact hc

private theorem p4Q2PY4B_fourthMoment_continuous :
    Continuous (fun A : Cfg => u A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 4),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 4⟩
  have hc := p4Q2PY4B_integral_first_continuous H f
  change Continuous (fun A : Cfg => u A) at hc
  exact hc

/-- Exact outer spatial-Haar decomposition of the true TWO-slab
fourth power SU(2) Wilson action, keeping the entire middle
spatial Wilson plaquette energy and all ordered crossing terms. -/
theorem p4Q2PY4_originalTwoSlabFourthHaar_split (B : Cfg) :
    v B = (∫ A : Cfg, u A ∂haar) -
      4 * (∫ A : Cfg, S A B * c A ∂haar) +
      6 * (∫ A : Cfg, (S A B) ^ 2 * b A ∂haar) -
      4 * (∫ A : Cfg, (S A B) ^ 3 * a A ∂haar) + u B := by
  have hRow := p4Q2PY4B_oneSlabAction_row_continuous H B
  have hA := p4Q2PY4B_firstMoment_continuous H
  have hB := p4Q2PY4B_secondMoment_continuous H
  have hC := p4Q2PY4B_thirdMoment_continuous H
  have hU := p4Q2PY4B_fourthMoment_continuous H
  have hiU : Integrable (fun A : Cfg => u A) haar :=
    hU.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiSC : Integrable (fun A : Cfg => S A B * c A) haar :=
    (hRow.mul hC).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS2b : Integrable (fun A : Cfg => (S A B) ^ 2 * b A) haar :=
    ((hRow.pow 2).mul hB).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS3a : Integrable (fun A : Cfg => (S A B) ^ 3 * a A) haar :=
    ((hRow.pow 3).mul hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS4 : Integrable (fun A : Cfg => (S A B) ^ 4) haar :=
    (hRow.pow 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiLeft : Integrable
      (fun A : Cfg => u A - 4 * (S A B * c A)) haar :=
    hiU.sub (hiSC.const_mul 4)
  have hiRight : Integrable
      (fun A : Cfg =>
        6 * ((S A B) ^ 2 * b A) - 4 * ((S A B) ^ 3 * a A)) haar :=
    (hiS2b.const_mul 6).sub (hiS3a.const_mul 4)
  have hiPair : Integrable (fun A : Cfg =>
      (u A - 4 * (S A B * c A)) +
        (6 * ((S A B) ^ 2 * b A) -
          4 * ((S A B) ^ 3 * a A))) haar :=
    hiLeft.add hiRight
  have hLast : (∫ A : Cfg, (S A B) ^ 4 ∂haar) = u B := rfl
  calc
    v B = (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 4 ∂haar ∂haar) := rfl
    _ = ∫ A : Cfg,
      ((u A - 4 * (S A B * c A)) +
        (6 * ((S A B) ^ 2 * b A) -
          4 * ((S A B) ^ 3 * a A))) + (S A B) ^ 4 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PY4_originalTwoSlabInnerQuartic_expansion H A B]
      ring
    _ = ((∫ A : Cfg, u A ∂haar) -
          4 * (∫ A : Cfg, S A B * c A ∂haar)) +
        (6 * (∫ A : Cfg, (S A B) ^ 2 * b A ∂haar) -
          4 * (∫ A : Cfg, (S A B) ^ 3 * a A ∂haar)) + u B := by
      rw [integral_add hiPair hiS4]
      rw [integral_add hiLeft hiRight]
      rw [integral_sub hiU (hiSC.const_mul 4)]
      rw [integral_sub (hiS2b.const_mul 6) (hiS3a.const_mul 4)]
      simp only [integral_const_mul, hLast]
    _ = _ := by ring

/-- TRUE first-action Haar centering transfers the mean(a) part
of the S^3-weighted term into exactly the negative third
one-slab action moment c(B). -/
private theorem p4Q2PY4B_centeredCubicActionHaar (B : Cfg) :
    (∫ A : Cfg, (S A B) ^ 3 * h A ∂haar) =
      (∫ A : Cfg, (S A B) ^ 3 * a A ∂haar) + m * c B := by
  have hRow := p4Q2PY4B_oneSlabAction_row_continuous H B
  have ha := p4Q2PY4B_firstMoment_continuous H
  have hiS3 : Integrable (fun A : Cfg => (S A B) ^ 3) haar :=
    (hRow.pow 3).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS3a : Integrable (fun A : Cfg => (S A B) ^ 3 * a A) haar :=
    ((hRow.pow 3).mul ha).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, (S A B) ^ 3 * h A ∂haar) =
      ∫ A : Cfg, (S A B) ^ 3 * a A - m * (S A B) ^ 3 ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        unfold p4Q2PS_originalCenteredFirstMoment
        ring
    _ = (∫ A : Cfg, (S A B) ^ 3 * a A ∂haar) -
        m * (∫ A : Cfg, (S A B) ^ 3 ∂haar) := by
        rw [integral_sub hiS3a (hiS3.const_mul m),
          integral_const_mul]
    _ = (∫ A : Cfg, (S A B) ^ 3 * a A ∂haar) + m * c B := by
        unfold p4Q2PP2_originalOneSlabThirdActionMoment
        ring

/-- First physical fifth Ward Haar decomposition:
the original fourth moments and cubic-jet counterterms collapse
to a single centered S^3 term, with FULL original Wilson S. -/
theorem p4Q2PY4_originalFifthWardResidual_centeredActionSplit (B : Cfg) :
    R5 B = (∫ A : Cfg, u A ∂haar) -
      4 * (∫ A : Cfg, S A B * c A ∂haar) +
      6 * (∫ A : Cfg, (S A B) ^ 2 * b A ∂haar) -
      4 * (∫ A : Cfg, (S A B) ^ 3 * h A ∂haar) -
      2 * s * b B := by
  have hOuter := p4Q2PY4_originalTwoSlabFourthHaar_split H B
  have hCentered := p4Q2PY4B_centeredCubicActionHaar H B
  unfold p4Q2PY_originalFifthWardResidual
  rw [hOuter, hCentered]
  ring

end OriginalFifthWardHaarResidualSplit
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY4_originalTwoSlabFourthHaar_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY4_originalFifthWardResidual_centeredActionSplit
