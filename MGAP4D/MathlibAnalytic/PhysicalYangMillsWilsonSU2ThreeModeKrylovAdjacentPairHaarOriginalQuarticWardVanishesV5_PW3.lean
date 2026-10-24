import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenteredFirstPlaquetteSumV5_PW2
import Mathlib.Tactic

/-!
# P4-Q2-PW3 — unconditional fourth-order Ward vanishing in the true SU(2) Wilson model

PW2 proves the ACTUAL centered one-slab Wilson Haar profile is
  a(A)-mean(a) = (1/2) * sum_{spatial p} χ_p(A).
PW proves every TRUE spatial plaquette χ_p is orthogonal under
the ORIGINAL full spatial Haar to the SQUARE of the complete
temporal crossing Wilson action, including all diagonal crossing
pairs, with the entire original SU(2) lattice preserved.

Exact compact-Haar finite-sum integration therefore proves the
PT3 two-crossing Ward profile
  P(B) = ∫ Cross(A,B)^2 * (a(A)-mean(a)) dHaar(A)
is IDENTICALLY ZERO at every finite even spatial SU(2) volume.

The full genuine original Wilson quartic coefficient C4 is zero for
EVERY actual three-configuration triple (A,B,C) by PT3's proved
identity. PP5's original literal Wilson minor therefore has O(beta^5)
behavior. This does NOT prove the physical third Hankel determinant
positive: the true fifth-order coefficient and higher terms remain
a separate unresolved analytic/frontier question.

No rank hypothesis, new axiom, sorry/admit, independent posterior,
Dobrushin hypothesis, spectral surrogate or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PW3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PW3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PW3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PW3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PW3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
namespace GroundStatePosteriorJoint

section ActualWilsonQuarticWardZero
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "P" => p4Q2PT2_originalTwoCrossingCenteredHaar H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

/-- The actual centered two-crossing Haar Ward profile vanishes
without ANY physical independent-Haar or rank assumption. -/
theorem p4Q2PW3_originalTwoCrossingCenteredHaar_zero (B : Cfg) :
    P B = 0 := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hInt (p : Plaq) :
      Integrable (fun A : Cfg =>
        χ p A * (Cross A B) ^ 2) haar :=
    ((p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul
      (hCross.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      (Cross A B) ^ 2 * ((1 / 2 : ℝ) * Φ A) =
        (1 / 2 : ℝ) *
          (∑ p : Plaq, χ p A * (Cross A B) ^ 2) := by
    calc
      (Cross A B) ^ 2 * ((1 / 2 : ℝ) * Φ A) =
          (1 / 2 : ℝ) *
            ((∑ p : Plaq, χ p A) * (Cross A B) ^ 2) := by
        unfold p4Q2PW2_originalAllPlaquetteRealTrace
        ring
      _ = (1 / 2 : ℝ) *
          (∑ p : Plaq, χ p A * (Cross A B) ^ 2) := by
        rw [Finset.sum_mul]
  change
    (∫ A : Cfg, (Cross A B) ^ 2 * h A ∂haar) = 0
  calc
    (∫ A : Cfg, (Cross A B) ^ 2 * h A ∂haar) =
        ∫ A : Cfg, (1 / 2 : ℝ) *
          (∑ p : Plaq, χ p A * (Cross A B) ^ 2) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A]
      exact hPoint A
    _ = (1 / 2 : ℝ) *
        (∫ A : Cfg,
          ∑ p : Plaq, χ p A * (Cross A B) ^ 2 ∂haar) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℝ) *
        (∑ p : Plaq,
          (∫ A : Cfg, χ p A * (Cross A B) ^ 2 ∂haar)) := by
      rw [integral_finset_sum _ (fun p _ => hInt p)]
    _ = 0 := by
      simp [p4Q2PW_originalPlaquetteChar_crossingSquareHaar_zero H]

/-- Unconditional vanishing of the ACTUAL complete original Wilson
quartic Haar coefficient, including the genuine cubic jet cross terms,
at EVERY original three-configuration triple and fixed finite H. -/
theorem p4Q2PW3_originalFourthCoefficient_zero
    (A B C : Cfg) :
    p4Q2PP2_originalFourthCoefficient H A B C = 0 := by
  have hDet :=
    p4Q2PT3_originalFourthCoefficient_twoCrossingMinor H A B C
  rw [p4Q2PW3_originalTwoCrossingCenteredHaar_zero H A,
    p4Q2PW3_originalTwoCrossingCenteredHaar_zero H B,
    p4Q2PW3_originalTwoCrossingCenteredHaar_zero H C] at hDet
  nlinarith

/-- The TRUE complete literal original Wilson three-spatial-boundary
minor is O(beta^5), not merely O(beta^4), at every fixed finite H
and every genuine triple A,B,C. No third Hankel rank is assumed. -/
theorem p4Q2PW3_originalLiteralWilsonMinor_fifthOrder
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
        ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C‖ ≤
          K * ‖beta‖ ^ 5 := by
  obtain ⟨K, hK, hRem⟩ :=
    p4Q2PP5_originalLiteralWilsonMinor_fourthCoefficient H A B C
  have hC4 := p4Q2PW3_originalFourthCoefficient_zero H A B C
  refine ⟨K, hK, ?_⟩
  intro beta hOne hBudget
  simpa [hC4] using hRem beta hOne hBudget

end ActualWilsonQuarticWardZero
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW3_originalTwoCrossingCenteredHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW3_originalFourthCoefficient_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW3_originalLiteralWilsonMinor_fifthOrder
