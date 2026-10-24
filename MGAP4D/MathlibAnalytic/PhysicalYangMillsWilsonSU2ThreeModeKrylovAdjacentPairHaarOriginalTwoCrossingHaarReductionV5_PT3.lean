import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoCrossingPointwiseV5_PT2
import Mathlib.Tactic

/-!
# P4-Q2-PT3 — original quartic Wilson coefficient reduced to two crossings

Combine PT's proven genuine gauge-weighted single-crossing Haar Ward
identity with PT2's exact pointwise action expansion. No posterior is
changed, and no nonzero coefficient or two-crossing vanishing is assumed.

The only surviving possible non-affine piece is
 P(B) = ∫ Cross(A,B)^2 * (a(A)-mean(a)) dHaar(A).
At every finite spatial H, the original Wilson fourth coefficient
is exactly the two-by-two minor of the genuine first moment and P.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PT3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PT3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PT3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PT3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PT3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalTwoCrossingHaarReduction
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "k" => p4Q2PT_originalSingleCrossingWardWeight H
local notation "F" => p4Q2PS_originalStrippedWardProfile H
local notation "P" => p4Q2PT2_originalTwoCrossingCenteredHaar H

/-- Original Haar-integrated exact split: pure spatial contribution,
single crossing, and a still-unresolved genuine two-crossing term. -/
theorem p4Q2PT3_originalStrippedWardHaar_split (B : Cfg) :
    F B =
      (∫ A : Cfg, (w A)^2 * h A - w A * b A ∂haar) +
      (∫ A : Cfg, k A * Cross A B ∂haar) + P B := by
  have hW : Continuous (fun A : Cfg => w A) := by
    change Continuous (fun A : Cfg => (1 / 2 : ℝ) * W A)
    exact continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hA : Continuous (fun A : Cfg => a A) := by
    have heq : (fun A : Cfg => a A) =
        (fun A : Cfg => -(1 / 2 : ℝ) * W A -
          p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) := by
      funext A
      exact p4Q2PM_originalFirstMoment_spatialWilson H A
    rw [heq]
    exact (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).sub
      continuous_const
  have hH : Continuous (fun A : Cfg => h A) := by
    change Continuous (fun A : Cfg => a A - p4Q2PQ_originalFirstActionMean H)
    exact hA.sub continuous_const
  have hB : Continuous (fun A : Cfg => b A) :=
    p4Q2PT_originalSecondMoment_continuous H
  have hK : Continuous (fun A : Cfg => k A) :=
    p4Q2PT_originalSingleCrossingWardWeight_continuous H
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hPure : Integrable
      (fun A : Cfg => (w A)^2 * h A - w A * b A) haar :=
    (((hW.pow 2).mul hH).sub (hW.mul hB)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSingle : Integrable (fun A : Cfg => k A * Cross A B) haar :=
    (hK.mul hCross).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDouble : Integrable (fun A : Cfg => (Cross A B)^2 * h A) haar :=
    ((hCross.pow 2).mul hH).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAdd1 :
      (∫ A : Cfg,
        ((w A)^2 * h A - w A * b A) + k A * Cross A B ∂haar) =
      (∫ A : Cfg, (w A)^2 * h A - w A * b A ∂haar) +
      (∫ A : Cfg, k A * Cross A B ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hPure hSingle)
  have hAdd2 :
      (∫ A : Cfg,
        (((w A)^2 * h A - w A * b A) + k A * Cross A B) +
          (Cross A B)^2 * h A ∂haar) =
      (∫ A : Cfg,
        ((w A)^2 * h A - w A * b A) + k A * Cross A B ∂haar) +
      (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add (hPure.add hSingle) hDouble)
  calc
    F B = ∫ A : Cfg,
        (((w A)^2 * h A - w A * b A) + k A * Cross A B) +
          (Cross A B)^2 * h A ∂haar := by
      unfold p4Q2PS_originalStrippedWardProfile
      apply integral_congr_ae
      filter_upwards with A
      exact p4Q2PT2_originalWardIntegrand_crossingExpansion H A B
    _ = (∫ A : Cfg,
        ((w A)^2 * h A - w A * b A) + k A * Cross A B ∂haar) +
      (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) := hAdd2
    _ = (∫ A : Cfg, (w A)^2 * h A - w A * b A ∂haar) +
      (∫ A : Cfg, k A * Cross A B ∂haar) + P B := by
      rw [hAdd1]
      rfl

/-- The only right-boundary variation of the full stripped Wilson
Ward residual is the centered TWO-crossing Haar moment P. -/
theorem p4Q2PT3_originalStrippedWard_difference_eq_twoCrossing
    (A B : Cfg) :
    F B - F A = P B - P A := by
  rw [p4Q2PT3_originalStrippedWardHaar_split H B,
    p4Q2PT3_originalStrippedWardHaar_split H A,
    p4Q2PT_originalSingleCrossingWardHaar_invariant H B,
    p4Q2PT_originalSingleCrossingWardHaar_invariant H A]
  ring

/-- Full original SU(2) Wilson fourth coefficient expressed solely
in genuine first action-moment differences and TWO crossing Haar. -/
theorem p4Q2PT3_originalFourthCoefficient_twoCrossingMinor
    (A B C : Cfg) :
    2 * p4Q2PP2_originalFourthCoefficient H A B C =
      (a B - a A) * (P C - P A) -
        (a C - a A) * (P B - P A) := by
  rw [p4Q2PS_originalFourthCoefficient_reducedStrippedMinor H A B C,
    p4Q2PT3_originalStrippedWard_difference_eq_twoCrossing H A C,
    p4Q2PT3_originalStrippedWard_difference_eq_twoCrossing H A B]

/-- Conditional logical consequence only: an eventual exact Ward
vanishing of P makes the true fourth coefficient vanish. -/
theorem p4Q2PT3_fourthCoefficient_zero_of_twoCrossing_constant
    (hP : ∀ B : Cfg, P B = P (fun _ => 1))
    (A B C : Cfg) :
    p4Q2PP2_originalFourthCoefficient H A B C = 0 := by
  have hMinor := p4Q2PT3_originalFourthCoefficient_twoCrossingMinor H A B C
  rw [hP A, hP B, hP C] at hMinor
  nlinarith

end OriginalTwoCrossingHaarReduction
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT3_originalStrippedWardHaar_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT3_originalStrippedWard_difference_eq_twoCrossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT3_originalFourthCoefficient_twoCrossingMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT3_fourthCoefficient_zero_of_twoCrossing_constant
