import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoSlabFifthCubicWardResidualV5_PZ14
import Mathlib.Tactic

/-!
# P4-Q2-PZ15 — physical fifth-action boundary polarization of the Ward residual

For the UNCHANGED original SU(2) Wilson one-slab action S(X,B) and
fully interacting two-slab action Q(X,A,B)=S(X,A)+S(A,B), the identity

  u^5-v^5 = (u-v)*(u^4+u^3*v+u^2*v^2+u*v^3+v^4)

factorizes all fifth-moment boundary differences. The genuine one-
and two-slab boundary differences are both exactly the integrals of
this fourth-degree polarization against the ORIGINAL boundary action
difference w(B)-w(C)+Cross(A,B)-Cross(A,C).

PZ12-PZ14 Ward invariance transports this exact physical response
to the difference of the two TRUE fifth-moment residuals r2-r1 and
hence to the corrected sixth Wilson obstruction W6.

The intermediate spatial Wilson action S(X,A), both Haar integrals
and true right-boundary Wilson terms remain unchanged throughout.
No posterior factorization, surrogate, unproved nonzero hypothesis,
new axiom, sorry or admit. This is an exact physical response formula,
not a proof W6 vanishes or is nonzero, nor a mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ15_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ15_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ15_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ15_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ15_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ15_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ15_productProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalFifthBoundaryPolarization

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "m5" => p4Q2PZ1_originalOneSlabFifthActionMoment H
local notation "n5" => p4Q2PZ1_originalTwoSlabFifthActionMoment H
local notation "r1" => p4Q2PZ13_originalOneSlabFifthResidual H
local notation "r2" => p4Q2PZ14_originalTwoSlabFifthResidual H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

/-- Exact fourth-degree polarization of a fifth-power difference. -/
def p4Q2PZ15_originalFourthPolarization (u v : ℝ) : ℝ :=
  u^4 + u^3*v + u^2*v^2 + u*v^3 + v^4

theorem p4Q2PZ15_originalFifthPower_polarization (u v : ℝ) :
    u^5 - v^5 =
      (u-v) * p4Q2PZ15_originalFourthPolarization u v := by
  unfold p4Q2PZ15_originalFourthPolarization
  ring

/-- Complete original one-slab right-boundary action difference. -/
theorem p4Q2PZ15_originalOneSlabAction_boundaryDifference (X B C : Cfg) :
    S X B - S X C = (w B - w C) + (Cross X B - Cross X C) := by
  rw [p4Q2PS_originalOneSlabAction_rightSplit H X B,
    p4Q2PS_originalOneSlabAction_rightSplit H X C]
  ring

/-- The original middle spatial plaquette action cancels ONLY
in the difference of the two complete two-slab actions. -/
theorem p4Q2PZ15_originalTwoSlabAction_boundaryDifference
    (X A B C : Cfg) :
    Q X A B - Q X A C =
      (w B - w C) + (Cross A B - Cross A C) := by
  change (S X A + S A B) - (S X A + S A C) = _
  rw [p4Q2PS_originalOneSlabAction_rightSplit H A B,
    p4Q2PS_originalOneSlabAction_rightSplit H A C]
  ring

/-- Exact boundary factor for the fifth power of the FULL interacting
two-slab Wilson action. The fourth-degree factor still contains S(X,A). -/
theorem p4Q2PZ15_originalTwoSlabFifth_boundaryFactor
    (X A B C : Cfg) :
    (Q X A B)^5 - (Q X A C)^5 =
      ((w B-w C) + (Cross A B-Cross A C)) *
        p4Q2PZ15_originalFourthPolarization (Q X A B) (Q X A C) := by
  rw [p4Q2PZ15_originalFifthPower_polarization]
  rw [p4Q2PZ15_originalTwoSlabAction_boundaryDifference H X A B C]

/-- Exact boundary factor for the original one-slab fifth power. -/
theorem p4Q2PZ15_originalOneSlabFifth_boundaryFactor
    (X B C : Cfg) :
    (S X B)^5 - (S X C)^5 =
      ((w B-w C) + (Cross X B-Cross X C)) *
        p4Q2PZ15_originalFourthPolarization (S X B) (S X C) := by
  rw [p4Q2PZ15_originalFifthPower_polarization]
  rw [p4Q2PZ15_originalOneSlabAction_boundaryDifference H X B C]

private theorem p4Q2PZ15_slab_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  have hCont :=
    (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

private theorem p4Q2PZ15_twoSlab_continuous_pair (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  have hSlab : Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
    p4Q2IW_originalWilsonOneSlabAction_continuous H
  have hPair : Continuous (fun A : Cfg => (A,B)) :=
    continuous_id.prodMk continuous_const
  have hRow : Continuous (fun A : Cfg => S A B) := by
    have hCont :=
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hCont
  change Continuous (fun p : Cfg × Cfg => S p.1 p.2 + S p.2 B)
  exact hSlab.add (hRow.comp continuous_snd)

private theorem p4Q2PZ15_twoSlab_continuous_inner (A B : Cfg) :
    Continuous (fun X : Cfg => Q X A B) := by
  have hPair : Continuous (fun X : Cfg => (X,A)) :=
    continuous_id.prodMk continuous_const
  have hCont := (p4Q2PZ15_twoSlab_continuous_pair H B).comp hPair
  simpa only [Function.comp_def] using hCont

private theorem p4Q2PZ15_twoSlab_continuous_outer (B : Cfg) :
    Continuous (fun A : Cfg => ∫ X : Cfg, (Q X A B)^5 ∂haar) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (Q p.1 p.2 B)^5),
      (p4Q2PZ15_twoSlab_continuous_pair H B).pow 5⟩
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun X : Cfg => v X) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X,A) ∂haar) =
      (fun A : Cfg => (∫ X : Cfg, v X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hv A]
    rfl
  change Continuous (fun A : Cfg => ∫ X : Cfg, f (X,A) ∂haar)
  rw [hfun]
  exact (∫ X : Cfg, v X ∂haar).continuous

/-- True one-slab fifth-moment boundary response, not a decoupled
measure or a substituted Wilson action. -/
noncomputable def p4Q2PZ15_originalOneSlabFifthBoundaryResponse
    (B C : Cfg) : ℝ :=
  ∫ X : Cfg,
    ((w B-w C) + (Cross X B-Cross X C)) *
      p4Q2PZ15_originalFourthPolarization (S X B) (S X C) ∂haar

/-- True two-slab fifth-moment boundary response with BOTH original
Haar integrals and the whole interacting middle slice. -/
noncomputable def p4Q2PZ15_originalTwoSlabFifthBoundaryResponse
    (B C : Cfg) : ℝ :=
  ∫ A : Cfg, ∫ X : Cfg,
    ((w B-w C) + (Cross A B-Cross A C)) *
      p4Q2PZ15_originalFourthPolarization (Q X A B) (Q X A C) ∂haar ∂haar

local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "J2" => p4Q2PZ15_originalTwoSlabFifthBoundaryResponse H

theorem p4Q2PZ15_originalOneSlabFifth_difference_response
    (B C : Cfg) :
    m5 B - m5 C = J1 B C := by
  have hi (D : Cfg) :
      Integrable (fun X : Cfg => (S X D)^5) haar :=
    ((p4Q2PZ15_slab_continuous H D).pow 5).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold p4Q2PZ1_originalOneSlabFifthActionMoment
    p4Q2PZ15_originalOneSlabFifthBoundaryResponse
  calc
    (∫ X : Cfg, (S X B)^5 ∂haar) -
      (∫ X : Cfg, (S X C)^5 ∂haar) =
        ∫ X : Cfg, (S X B)^5 - (S X C)^5 ∂haar := by
          exact (integral_sub (hi B) (hi C)).symm
    _ = ∫ X : Cfg,
          ((w B-w C) + (Cross X B-Cross X C)) *
            p4Q2PZ15_originalFourthPolarization (S X B) (S X C)
          ∂haar := by
            apply integral_congr_ae
            filter_upwards with X
            exact p4Q2PZ15_originalOneSlabFifth_boundaryFactor H X B C

theorem p4Q2PZ15_originalTwoSlabFifth_difference_response
    (B C : Cfg) :
    n5 B - n5 C = J2 B C := by
  have hiInner (D A : Cfg) :
      Integrable (fun X : Cfg => (Q X A D)^5) haar :=
    ((p4Q2PZ15_twoSlab_continuous_inner H A D).pow 5).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiOuter (D : Cfg) :
      Integrable (fun A : Cfg => ∫ X : Cfg, (Q X A D)^5 ∂haar) haar :=
    (p4Q2PZ15_twoSlab_continuous_outer H D).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold p4Q2PZ1_originalTwoSlabFifthActionMoment
    p4Q2PZ15_originalTwoSlabFifthBoundaryResponse
  calc
    (∫ A : Cfg, ∫ X : Cfg, (Q X A B)^5 ∂haar ∂haar) -
      (∫ A : Cfg, ∫ X : Cfg, (Q X A C)^5 ∂haar ∂haar) =
        ∫ A : Cfg,
          (∫ X : Cfg, (Q X A B)^5 ∂haar) -
            (∫ X : Cfg, (Q X A C)^5 ∂haar) ∂haar := by
              exact (integral_sub (hiOuter B) (hiOuter C)).symm
    _ = ∫ A : Cfg, ∫ X : Cfg,
          (Q X A B)^5 - (Q X A C)^5 ∂haar ∂haar := by
            apply integral_congr_ae
            filter_upwards with A
            exact (integral_sub (hiInner B A) (hiInner C A)).symm
    _ = ∫ A : Cfg, ∫ X : Cfg,
          ((w B-w C) + (Cross A B-Cross A C)) *
            p4Q2PZ15_originalFourthPolarization (Q X A B) (Q X A C)
          ∂haar ∂haar := by
            apply integral_congr_ae
            filter_upwards with A
            apply integral_congr_ae
            filter_upwards with X
            exact p4Q2PZ15_originalTwoSlabFifth_boundaryFactor H X A B C

/-- Physical response gap: full TWO-slab Haar response minus true
ONE-slab Haar response, with all common Ward-invariant cubic sectors
already removed by PZ12-PZ14. -/
noncomputable def p4Q2PZ15_originalWardResidualResponseGap
    (B C : Cfg) : ℝ :=
  J2 B C - J1 B C

local notation "G" => p4Q2PZ15_originalWardResidualResponseGap H

/-- Exact Ward-transport of BOTH true fifth moment residuals to
physical fourth-polarization Haar response functionals. -/
theorem p4Q2PZ15_originalResidualGap_boundaryResponse
    (B C : Cfg) :
    (r2 B-r1 B) - (r2 C-r1 C) = G B C := by
  calc
    (r2 B-r1 B) - (r2 C-r1 C) =
        (r2 B-r2 C) - (r1 B-r1 C) := by ring
    _ = (n5 B-n5 C) - (m5 B-m5 C) := by
      rw [← p4Q2PZ14_originalTwoSlabFifth_difference_residual H C B,
          ← p4Q2PZ13_originalOneSlabFifth_difference_residual H C B]
    _ = J2 B C - J1 B C := by
      rw [p4Q2PZ15_originalTwoSlabFifth_difference_response H B C,
          p4Q2PZ15_originalOneSlabFifth_difference_response H B C]
    _ = G B C := rfl

/-- Genuine W6 is the fourth-jet coefficient minus the alternating
determinant of the exact, fully interacting physical boundary
responses. No claim of universal vanishing or nonvanishing. -/
theorem p4Q2PZ15_originalSixthWard_physicalBoundaryResponse
    (A B C : Cfg) :
    W6 A B C =
      720 * C6 A B C -
        6 * ((a B-a A) * G C A - (a C-a A) * G B A) := by
  have hC :
      ((r2 C-r2 A) - (r1 C-r1 A)) = G C A := by
    calc
      ((r2 C-r2 A) - (r1 C-r1 A)) =
        (r2 C-r1 C) - (r2 A-r1 A) := by ring
      _ = G C A := p4Q2PZ15_originalResidualGap_boundaryResponse H C A
  have hB :
      ((r2 B-r2 A) - (r1 B-r1 A)) = G B A := by
    calc
      ((r2 B-r2 A) - (r1 B-r1 A)) =
        (r2 B-r1 B) - (r2 A-r1 A) := by ring
      _ = G B A := p4Q2PZ15_originalResidualGap_boundaryResponse H B A
  rw [p4Q2PZ14_originalSixthWard_doubleResidual H A B C,
    hC, hB]
  ring

end OriginalFifthBoundaryPolarization
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalFifthPower_polarization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalTwoSlabAction_boundaryDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalTwoSlabFifth_boundaryFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalOneSlabFifth_difference_response
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalTwoSlabFifth_difference_response
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalResidualGap_boundaryResponse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ15_originalSixthWard_physicalBoundaryResponse
