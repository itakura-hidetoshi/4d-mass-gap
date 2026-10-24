import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralSixthCoefficientV5_PZ7
import Mathlib.Tactic

/-!
# P4-Q2-PZ8 — exact sixth Ward gate and physical small-coupling nonzero transfer

The genuine one/two-slab SU(2) Wilson action and the original Haar
measures remain unchanged. PZ1/PZ7 express the literal minor as
beta^6 * D6 plus a proved seventh-order remainder.

This file exposes the precise original-action-moment sixth Ward
obstruction W6 = 720 * D6, proves its ZERO/NONZERO decision gate,
and transports either answer to the literal interacting Wilson minor:
* W6 = 0 gives the actual seventh-order upper bound.
* W6 ≠ 0 gives a positive small-coupling interval of NONZERO literal
  minors, using PZ7's genuine uniform-in-beta finite-volume remainder.

The existence of a physical triple with W6 ≠ 0, or universal
vanishing of W6, is NOT assumed or claimed. Nor does a conditional
literal minor witness establish a mass gap or volume-uniform U0.
No new axioms, sorry/admit, posterior substitutes or spectral proxies.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalSixthWardDecision

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H
local notation "m" => p4Q2PZ1_originalOneSlabFifthActionMoment H
local notation "n" => p4Q2PZ1_originalTwoSlabFifthActionMoment H
local notation "D6" => p4Q2PZ1_originalSixthFifthJetCoefficient H

/-- The exact SIXTH Ward obstruction in original interacting Haar
action moments. In particular, n is the real double-Haar moment of
S(X,A)+S(A,B), including ALL middle-slice spatial plaquettes. -/
noncomputable def p4Q2PZ8_originalSixthWardObstruction
    (A B C : Cfg) : ℝ :=
  20 * ((c B - c A) * (g C - g A) -
    (c C - c A) * (g B - g A)) +
  15 * ((b B - b A) * (v C - v A) -
    (b C - b A) * (v B - v A)) +
  15 * ((u B - u A) * ((b C - b A) + 2 * (d C - d A)) -
    (u C - u A) * ((b B - b A) + 2 * (d B - d A))) -
  6 * ((a B - a A) * ((n C - n A) - (m C - m A)) -
    (a C - a A) * ((n B - n A) - (m B - m A)))

local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

/-- EXACT four-Haar-determinant Ward obstruction, not a formal
new independence assumption. -/
theorem p4Q2PZ8_sixthWard_eq_correctedCoefficient
    (A B C : Cfg) :
    W6 A B C = 720 * D6 A B C := by
  exact (p4Q2PZ1_originalSixthFifthJetCoefficient_fourDeterminants
    H A B C).symm

/-- A full sixth Ward cancellation is necessary and sufficient for
the genuine sixth-moment jet coefficient to vanish. -/
theorem p4Q2PZ8_sixthWard_zero_iff
    (A B C : Cfg) :
    W6 A B C = 0 ↔ D6 A B C = 0 := by
  rw [p4Q2PZ8_sixthWard_eq_correctedCoefficient H A B C]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    simp [h]

/-- Equivalently, a physical nonzero original Haar Ward obstruction
is exactly a nonzero corrected genuine sixth coefficient. -/
theorem p4Q2PZ8_sixthWard_nonzero_iff
    (A B C : Cfg) :
    W6 A B C ≠ 0 ↔ D6 A B C ≠ 0 := by
  simpa only [ne_eq] using
    not_congr (p4Q2PZ8_sixthWard_zero_iff H A B C)

/-- If the sixth Haar Ward obstruction cancels, the actual literal
interacting Wilson minor has an O(beta^7) remainder. -/
theorem p4Q2PZ8_originalLiteralMinor_seventhOrder_of_sixthWardZero
    (A B C : Cfg) (hWard : W6 A B C = 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C‖ ≤
            K * ‖beta‖ ^ 7 := by
  have hD6 : D6 A B C = 0 :=
    (p4Q2PZ8_sixthWard_zero_iff H A B C).mp hWard
  obtain ⟨K, hK, hRem⟩ :=
    p4Q2PZ7_originalLiteralWilsonMinor_sixthCoefficient H A B C
  refine ⟨K, hK, ?_⟩
  intro beta hBeta hSmall
  have h := hRem beta hBeta hSmall
  rw [hD6, mul_zero, sub_zero] at h
  exact h

/-- A strict coefficient-vs-remainder inequality certifies an actual
NONZERO literal Wilson three-spatial-configuration minor. All bounds
are finite-volume physical action bounds from PZ7. -/
theorem p4Q2PZ8_originalLiteralMinor_nonzero_of_strictSixthWitness
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, 0 < ‖beta‖ →
        ‖beta‖ ≤ 1 → ‖beta * (2 * M)‖ ≤ 1 →
          K * ‖beta‖ < ‖D6 A B C‖ →
            p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C ≠ 0 := by
  obtain ⟨K, hK, hRem⟩ :=
    p4Q2PZ7_originalLiteralWilsonMinor_sixthCoefficient H A B C
  refine ⟨K, hK, ?_⟩
  intro beta hBeta hBetaOne hSmall hStrict hZero
  have h := hRem beta hBetaOne hSmall
  rw [hZero, zero_sub, norm_neg, norm_mul, norm_pow] at h
  have hPow : 0 < ‖beta‖ ^ 6 := pow_pos hBeta 6
  have hScaled :
      ‖beta‖ ^ 6 * ‖D6 A B C‖ ≤
        ‖beta‖ ^ 6 * (K * ‖beta‖) := by
    calc
      ‖beta‖ ^ 6 * ‖D6 A B C‖ ≤ K * ‖beta‖ ^ 7 := h
      _ = ‖beta‖ ^ 6 * (K * ‖beta‖) := by ring
  have hBound : ‖D6 A B C‖ ≤ K * ‖beta‖ :=
    le_of_mul_le_mul_left hScaled hPow
  exact (not_lt_of_ge hBound) hStrict

/-- If a genuine SU(2) triple has W6 ≠ 0, EVERY sufficiently
small positive fine coupling produces a NONZERO literal Wilson
minor. A witness for W6 is still a separate geometric/Haar task. -/
theorem p4Q2PZ8_originalLiteralMinor_smallPositive_nonzero_of_Ward
    (A B C : Cfg) (hWard : W6 A B C ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ beta : ℝ, 0 < beta → beta < delta →
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C ≠ 0 := by
  have hD : D6 A B C ≠ 0 :=
    (p4Q2PZ8_sixthWard_nonzero_iff H A B C).mp hWard
  obtain ⟨K, hK, hCert⟩ :=
    p4Q2PZ8_originalLiteralMinor_nonzero_of_strictSixthWitness H A B C
  let mBudget : ℝ := ‖2 * M‖
  let delta : ℝ :=
    min 1 (min (1 / (1 + mBudget)) (‖D6 A B C‖ / (K + 1)))
  have hm : 0 ≤ mBudget := norm_nonneg _
  have hKplus : 0 < K + 1 := by linarith
  have hMplus : 0 < 1 + mBudget := by linarith
  have hDpos : 0 < ‖D6 A B C‖ := norm_pos_iff.mpr hD
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min (by norm_num)
    exact lt_min (div_pos (by norm_num) hMplus) (div_pos hDpos hKplus)
  have hdeltaOne : delta ≤ 1 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdeltaBudget : delta ≤ 1 / (1 + mBudget) := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaD : delta ≤ ‖D6 A B C‖ / (K + 1) := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta, hdelta, ?_⟩
  intro beta hBeta hSmall
  have hBetaNorm : ‖beta‖ = beta := by
    rw [Real.norm_eq_abs, abs_of_pos hBeta]
  have hBetaPositive : 0 < ‖beta‖ := by
    rw [hBetaNorm]
    exact hBeta
  have hBetaOne : ‖beta‖ ≤ 1 := by
    rw [hBetaNorm]
    exact (le_of_lt (lt_of_lt_of_le hSmall hdeltaOne))
  have hBetaBudget : ‖beta * (2 * M)‖ ≤ 1 := by
    rw [norm_mul, hBetaNorm]
    have hBudgetLt : beta < 1 / (1 + mBudget) :=
      lt_of_lt_of_le hSmall hdeltaBudget
    have hTimes : beta * (1 + mBudget) < 1 :=
      (lt_div_iff₀ hMplus).mp hBudgetLt
    change beta * mBudget ≤ 1
    nlinarith
  have hStrict : K * ‖beta‖ < ‖D6 A B C‖ := by
    rw [hBetaNorm]
    have hDLt : beta < ‖D6 A B C‖ / (K + 1) :=
      lt_of_lt_of_le hSmall hdeltaD
    have hTimes : beta * (K + 1) < ‖D6 A B C‖ :=
      (lt_div_iff₀ hKplus).mp hDLt
    nlinarith [hBeta]
  exact hCert beta hBetaPositive hBetaOne hBetaBudget hStrict

end OriginalSixthWardDecision
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ8_sixthWard_eq_correctedCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ8_sixthWard_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ8_sixthWard_nonzero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ8_originalLiteralMinor_seventhOrder_of_sixthWardZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ8_originalLiteralMinor_nonzero_of_strictSixthWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ8_originalLiteralMinor_smallPositive_nonzero_of_Ward
