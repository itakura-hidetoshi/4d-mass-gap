import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthHaarResidualSplitV5_PY4B
import Mathlib.Tactic

/-!
# P4-Q2-PY4C — remove pure triple crossing from the TRUE fifth Ward residual

PY4B identifies the genuinely interacting one/two-slab fourth
Haar-moment fifth Ward residual with the centered S^3 weighted moment.
Expand the ORIGINAL full one-slab Wilson action pointwise:
  S(A,B)=w(A)+Cross(A,B)+w(B), w=W_spatial/2.

The full centered cubic moment contains three classes with 0,1,2
temporal crossings plus exactly ∫Cross(A,B)^3*h(A).
PY3C has unconditionally proved this last term ZERO under the
unchanged spatial SU(2) Haar at every finite periodic spatial volume.

Therefore the true fifth residual has a representation with at most
TWO explicit temporal crossing insertions in its centered cubic term.
Other authentic mixed Wilson Haar moments are retained, NOT assumed
affine or zero. No sorry, admit, extra axiom, spectral substitute,
Dobrushin or unproved third-Hankel positivity.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY4C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY4C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY4C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY4C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY4C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalFifthWardTwoCrossingCore
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
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "s" => p4Q2PY_originalQuarticWardSlope H
local notation "R5" => p4Q2PY_originalFifthWardResidual H

/-- The centered full SU(2) S^3 Haar term equals its genuine
zero-, one-, and two-crossing components after the PROVED true
center-odd triple-crossing Haar cancellation. -/
theorem p4Q2PY4_originalCenteredCubicAction_noThreeCrossing
    (B : Cfg) :
    (∫ A : Cfg, (S A B) ^ 3 * h A ∂haar) =
    (∫ A : Cfg,
      ((w A + w B) ^ 3 +
        3 * (w A + w B) ^ 2 * Cross A B +
        3 * (w A + w B) * (Cross A B) ^ 2) * h A ∂haar) := by
  let z : Cfg → ℝ := fun A => w A + w B
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hz : Continuous z := hw.add continuous_const
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have ha : Continuous (fun A : Cfg => a A) := by
    have heq : (fun A : Cfg => a A) =
      fun A : Cfg => -(1 / 2 : ℝ) * W A -
        p4Q2JE_originalWilsonHaarZeroDerivativeConstant H := by
      funext A
      exact p4Q2PM_originalFirstMoment_spatialWilson H A
    rw [heq]
    exact (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).sub
      continuous_const
  have hh : Continuous (fun A : Cfg => h A) := by
    change Continuous (fun A : Cfg =>
      a A - p4Q2PQ_originalFirstActionMean H)
    exact ha.sub continuous_const
  have hPoly : Continuous (fun A : Cfg =>
      (z A ^ 3 + 3 * z A ^ 2 * Cross A B +
        3 * z A * (Cross A B) ^ 2) * h A) := by
    exact
      (((hz.pow 3).add ((continuous_const.mul (hz.pow 2)).mul hCross)).add
        ((continuous_const.mul hz).mul (hCross.pow 2))).mul hh
  have hTriple : Continuous (fun A : Cfg =>
      (Cross A B) ^ 3 * h A) := (hCross.pow 3).mul hh
  have hiPoly : Integrable (fun A : Cfg =>
      (z A ^ 3 + 3 * z A ^ 2 * Cross A B +
        3 * z A * (Cross A B) ^ 2) * h A) haar :=
    hPoly.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiTriple : Integrable (fun A : Cfg =>
      (Cross A B) ^ 3 * h A) haar :=
    hTriple.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      (S A B) ^ 3 * h A =
      (z A ^ 3 + 3 * z A ^ 2 * Cross A B +
        3 * z A * (Cross A B) ^ 2) * h A +
      (Cross A B) ^ 3 * h A := by
    rw [p4Q2PS_originalOneSlabAction_rightSplit H A B]
    unfold p4Q2PS_originalRightStrippedAction
    dsimp [z]
    ring
  have hZero :
      (∫ A : Cfg, (Cross A B) ^ 3 * h A ∂haar) = 0 :=
    p4Q2PY3_originalThreeCrossingCenteredHaar_zero H B
  calc
    (∫ A : Cfg, (S A B) ^ 3 * h A ∂haar) =
        ∫ A : Cfg,
          (z A ^ 3 + 3 * z A ^ 2 * Cross A B +
            3 * z A * (Cross A B) ^ 2) * h A +
            (Cross A B) ^ 3 * h A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = (∫ A : Cfg,
      (z A ^ 3 + 3 * z A ^ 2 * Cross A B +
        3 * z A * (Cross A B) ^ 2) * h A ∂haar) +
      (∫ A : Cfg, (Cross A B) ^ 3 * h A ∂haar) := by
      simpa only [Pi.add_apply] using (integral_add hiPoly hiTriple)
    _ = (∫ A : Cfg,
      ((w A + w B) ^ 3 +
        3 * (w A + w B) ^ 2 * Cross A B +
        3 * (w A + w B) * (Cross A B) ^ 2) * h A ∂haar) := by
      dsimp only [z]
      rw [hZero, add_zero]

/-- Complete ORIGINAL fifth SU(2) Wilson Haar Ward residual after
the actual triple-crossing Haar selection rule: its centered S^3
piece now contains at most two crossing factors, while every other
original action moment remains unchanged and interacting. -/
theorem p4Q2PY4_originalFifthWardResidual_noPureThreeCrossing
    (B : Cfg) :
    R5 B =
      (∫ A : Cfg, u A ∂haar) -
      4 * (∫ A : Cfg, S A B * c A ∂haar) +
      6 * (∫ A : Cfg, (S A B) ^ 2 * b A ∂haar) -
      4 * (∫ A : Cfg,
        ((w A + w B) ^ 3 +
          3 * (w A + w B) ^ 2 * Cross A B +
          3 * (w A + w B) * (Cross A B) ^ 2) * h A ∂haar) -
      2 * s * b B := by
  rw [p4Q2PY4_originalFifthWardResidual_centeredActionSplit H B,
    p4Q2PY4_originalCenteredCubicAction_noThreeCrossing H B]

end OriginalFifthWardTwoCrossingCore
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY4_originalCenteredCubicAction_noThreeCrossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY4_originalFifthWardResidual_noPureThreeCrossing
