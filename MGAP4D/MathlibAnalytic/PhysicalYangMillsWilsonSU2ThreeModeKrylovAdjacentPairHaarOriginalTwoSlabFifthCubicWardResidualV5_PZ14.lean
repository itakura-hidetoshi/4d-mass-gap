import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthMomentCubicWardResidualV5_PZ13
import Mathlib.Tactic

/-!
# P4-Q2-PZ14 — full interacting TWO-SLAB fifth Wilson Haar Ward residual

The ORIGINAL Wilson two-slab action is retained IDENTICALLY:
 Q(X,A,B) = S(X,A)+S(A,B)
          = S(X,A)+w(A)+Cross(A,B)+w(B).
It contains the full spatial Wilson plaquette at intermediate A.
Its fifth power has the EXACT centered-cubic term
  10*h(A)^2*Cross(A,B)^3,
whose genuine SU(2) double Haar mean reduces to PZ12's original
right-boundary invariant centered cubic Haar moment. The remaining
fifth-degree polynomial retains S(X,A) with all original interactions.

Thus n5(B)-n5(A) is exactly the difference of the true double-Haar
residual integrals. With PZ13, the corrected original D6 and W6 have
an explicit fifth-moment residual determinant containing NO
right-boundary-constant cubic-centered Ward terms.

This does not establish W6=0 or W6 != 0, D3>0, U0 or the mass gap.
No posterior factorization, new axiom, sorry, admit, or surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ14_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ14_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ14_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ14_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ14_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ14_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ14_productProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalTwoSlabFifthWardResidual
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "Phi" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "n5" => p4Q2PZ1_originalTwoSlabFifthActionMoment H
local notation "G3" => p4Q2PZ13_originalCenteredCubicHaar H
local notation "r1" => p4Q2PZ13_originalOneSlabFifthResidual H

/-- Exact fifth-degree remainder of the fully interacting original
two-slab action. The left factor S(X,A) includes the ORIGINAL
intermediate spatial plaquette half-weight, not a posterior proxy. -/
noncomputable def p4Q2PZ14_originalTwoSlabFifthResidualIntegrand
    (X A B : Cfg) : ℝ :=
  let r : ℝ := S X A + w A + w B
  let z : ℝ := S X A + (∫ Y : Cfg, w Y ∂haar) + w B
  let c : ℝ := Cross A B
  r^5 + 5 * r^4 * c + 10 * r^3 * c^2 +
    10 * (z^2 - 2 * z * h A) * c^3 +
      5 * r * c^4 + c^5

local notation "R2" =>
  p4Q2PZ14_originalTwoSlabFifthResidualIntegrand H

/-- Exact ORIGINAL two-slab fifth action decomposition. All
left-slab Wilson factors, middle spatial plaquettes and both
crossing actions are unchanged. -/
theorem p4Q2PZ14_originalTwoSlabFifth_split
    (X A B : Cfg) :
    (Q X A B)^5 =
      10 * ((h A)^2 * (Cross A B)^3) + R2 X A B := by
  change (S X A + S A B)^5 =
    10 * ((h A)^2 * (Cross A B)^3) + R2 X A B
  rw [p4Q2PS_originalOneSlabAction_rightSplit H A B]
  change (S X A + (w A + Cross A B + w B))^5 =
    10 * ((h A)^2 * (Cross A B)^3) + R2 X A B
  unfold p4Q2PZ14_originalTwoSlabFifthResidualIntegrand
  dsimp only
  rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H A]
  ring

private theorem p4Q2PZ14_integral_first_continuous
    (f : C(Cfg × Cfg, ℝ)) :
    Continuous (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) := by
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun X : Cfg => v X) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) =
        (fun A : Cfg => (∫ X : Cfg, v X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hv A]
    rfl
  rw [hfun]
  exact (∫ X : Cfg, v X ∂haar).continuous

private theorem p4Q2PZ14_centered_continuous :
    Continuous (fun A : Cfg => h A) := by
  have hEq :
      (fun A : Cfg => h A) =
        (fun A : Cfg => (1 / 2 : ℝ) * Phi A) := by
    funext A
    exact p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A
  rw [hEq]
  exact continuous_const.mul
    (p4Q2PW2_originalAllPlaquetteRealTrace_continuous H)

private theorem p4Q2PZ14_cross_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Cross A B) := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCont := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

private theorem p4Q2PZ14_Q_continuous (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  have hSlab : Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
    p4Q2IW_originalWilsonOneSlabAction_continuous H
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hRow : Continuous (fun A : Cfg => S A B) := by
    have hCont := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hCont
  change Continuous (fun p : Cfg × Cfg => S p.1 p.2 + S p.2 B)
  exact hSlab.add (hRow.comp continuous_snd)

private theorem p4Q2PZ14_R2_continuous (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => R2 p.1 p.2 B) := by
  have hQ : Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) :=
    p4Q2PZ14_Q_continuous H B
  have hh : Continuous (fun p : Cfg × Cfg => h p.2) :=
    (p4Q2PZ14_centered_continuous H).comp continuous_snd
  have hc : Continuous (fun p : Cfg × Cfg => Cross p.2 B) :=
    (p4Q2PZ14_cross_continuous H B).comp continuous_snd
  have heq :
      (fun p : Cfg × Cfg => R2 p.1 p.2 B) =
        (fun p : Cfg × Cfg =>
          (Q p.1 p.2 B)^5 -
            10 * ((h p.2)^2 * (Cross p.2 B)^3)) := by
    funext p
    have hp := p4Q2PZ14_originalTwoSlabFifth_split H p.1 p.2 B
    linear_combination -hp
  rw [heq]
  exact (hQ.pow 5).sub
    (continuous_const.mul ((hh.pow 2).mul (hc.pow 3)))

/-- Explicit true physical TWO-SLAB fifth residual under BOTH
original nested SU(2) Haar integrations, with the middle slice
fully retained. -/
noncomputable def p4Q2PZ14_originalTwoSlabFifthResidual
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, ∫ X : Cfg, R2 X A B ∂haar ∂haar

local notation "r2" => p4Q2PZ14_originalTwoSlabFifthResidual H

/-- The exact original interacting two-slab fifth Haar moment is
its PZ12-invariant genuine centered cubic sector plus the true
double-Haar fifth polynomial residual. -/
theorem p4Q2PZ14_originalTwoSlabFifth_eq_WardPlusResidual
    (B : Cfg) :
    n5 B = 10 * G3 B + r2 B := by
  let fR : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => R2 p.1 p.2 B), p4Q2PZ14_R2_continuous H B⟩
  have hOuterR :
      Integrable (fun A : Cfg => ∫ X : Cfg, R2 X A B ∂haar) haar :=
    (p4Q2PZ14_integral_first_continuous H fR).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh : Continuous (fun A : Cfg => h A) :=
    p4Q2PZ14_centered_continuous H
  have hc : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ14_cross_continuous H B
  have hOuterWard :
      Integrable
        (fun A : Cfg => (10 : ℝ) * ((h A)^2 * (Cross A B)^3)) haar :=
    (continuous_const.mul ((hh.pow 2).mul (hc.pow 3))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInnerR (A : Cfg) :
      Integrable (fun X : Cfg => R2 X A B) haar := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    exact ((p4Q2PZ14_R2_continuous H B).comp hPair).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInnerConst (A : Cfg) :
      (∫ X : Cfg,
        (10 : ℝ) * ((h A)^2 * (Cross A B)^3) ∂haar) =
        (10 : ℝ) * ((h A)^2 * (Cross A B)^3) := by
    simp
  have hInner (A : Cfg) :
      (∫ X : Cfg, (Q X A B)^5 ∂haar) =
        (10 : ℝ) * ((h A)^2 * (Cross A B)^3) +
          (∫ X : Cfg, R2 X A B ∂haar) := by
    have hiConst :
        Integrable
          (fun X : Cfg => (10 : ℝ) * ((h A)^2 * (Cross A B)^3))
          haar := integrable_const _
    calc
      (∫ X : Cfg, (Q X A B)^5 ∂haar) =
        ∫ X : Cfg,
          (10 : ℝ) * ((h A)^2 * (Cross A B)^3) + R2 X A B ∂haar := by
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ14_originalTwoSlabFifth_split H X A B
      _ = (∫ X : Cfg, (10 : ℝ) * ((h A)^2 * (Cross A B)^3) ∂haar) +
          (∫ X : Cfg, R2 X A B ∂haar) := by
          simpa only [Pi.add_apply] using
            (integral_add hiConst (hInnerR A))
      _ = (10 : ℝ) * ((h A)^2 * (Cross A B)^3) +
          (∫ X : Cfg, R2 X A B ∂haar) := by rw [hInnerConst A]
  calc
    n5 B =
        ∫ A : Cfg,
          (10 : ℝ) * ((h A)^2 * (Cross A B)^3) +
            (∫ X : Cfg, R2 X A B ∂haar) ∂haar := by
      unfold p4Q2PZ1_originalTwoSlabFifthActionMoment
      apply integral_congr_ae
      filter_upwards with A
      exact hInner A
    _ = (10 : ℝ) * (∫ A : Cfg, (h A)^2 * (Cross A B)^3 ∂haar) +
        (∫ A : Cfg, ∫ X : Cfg, R2 X A B ∂haar ∂haar) := by
      simpa only [Pi.add_apply, integral_const_mul] using
        (integral_add hOuterWard hOuterR)
    _ = 10 * G3 B + r2 B := rfl

/-- PZ12's genuine cubic centered Haar contribution cancels from
every right-boundary difference of the ORIGINAL double Haar n5. -/
theorem p4Q2PZ14_originalTwoSlabFifth_difference_residual
    (A B : Cfg) :
    n5 B - n5 A = r2 B - r2 A := by
  rw [p4Q2PZ14_originalTwoSlabFifth_eq_WardPlusResidual H B,
    p4Q2PZ14_originalTwoSlabFifth_eq_WardPlusResidual H A,
    p4Q2PZ13_originalCenteredCubicHaar_invariant H B,
    p4Q2PZ13_originalCenteredCubicHaar_invariant H A]
  ring

/-- The corrected SIXTH coefficient of the original Wilson minor
is exactly the fourth-jet C6 plus the genuine two-slab-minus-one-slab
RESIDUAL determinant. BOTH original Haar integrations and full
intermediate Wilson spatial plaquettes remain. -/
theorem p4Q2PZ14_originalSixthCoefficient_doubleResidual
    (A B C : Cfg) :
    p4Q2PZ1_originalSixthFifthJetCoefficient H A B C =
      p4Q2PX_originalSixthFourthJetCoefficient H A B C -
      ((p4Q2PK_originalOneSlabFirstActionMoment H B -
          p4Q2PK_originalOneSlabFirstActionMoment H A) *
        ((r2 C - r2 A) - (r1 C - r1 A)) -
       (p4Q2PK_originalOneSlabFirstActionMoment H C -
          p4Q2PK_originalOneSlabFirstActionMoment H A) *
        ((r2 B - r2 A) - (r1 B - r1 A))) / 120 := by
  rw [p4Q2PZ13_originalSixthCoefficient_oneSlabResidual H A B C,
    p4Q2PZ14_originalTwoSlabFifth_difference_residual H A C,
    p4Q2PZ14_originalTwoSlabFifth_difference_residual H A B]

/-- TRUE sixth Ward obstruction with ALL right-boundary-constant
cubic-centered terms removed from BOTH action fifth moments.
This is an identity, not a proof of unconditional vanishing. -/
theorem p4Q2PZ14_originalSixthWard_doubleResidual
    (A B C : Cfg) :
    p4Q2PZ8_originalSixthWardObstruction H A B C =
      720 * (p4Q2PX_originalSixthFourthJetCoefficient H A B C -
      ((p4Q2PK_originalOneSlabFirstActionMoment H B -
          p4Q2PK_originalOneSlabFirstActionMoment H A) *
        ((r2 C - r2 A) - (r1 C - r1 A)) -
       (p4Q2PK_originalOneSlabFirstActionMoment H C -
          p4Q2PK_originalOneSlabFirstActionMoment H A) *
        ((r2 B - r2 A) - (r1 B - r1 A))) / 120) := by
  rw [p4Q2PZ8_sixthWard_eq_correctedCoefficient H A B C,
    p4Q2PZ14_originalSixthCoefficient_doubleResidual H A B C]

end OriginalTwoSlabFifthWardResidual
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ14_originalTwoSlabFifth_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ14_originalTwoSlabFifth_eq_WardPlusResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ14_originalTwoSlabFifth_difference_residual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ14_originalSixthCoefficient_doubleResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ14_originalSixthWard_doubleResidual
