import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourthWardResidualV5_PQ
import Mathlib.Tactic

/-!
# P4-Q2-PQ2 — exact Wilson quartic witness-to-third-Hankel bridge

PP5 proves the LITERAL ORIGINAL two-slab Wilson three-boundary minor
equals beta^4 times its full fourth Haar coefficient up to a fifth
order remainder, with no changed reference Haar or physical transfer.

We prove that ANY genuinely constructed nonzero fourth coefficient
at a triple of actual SU(2) spatial configurations yields a uniform
nonzero literal minor for all sufficiently small positive beta.
Combined with PJ's genuine Schur/Hankel iff and an independently
proved D2>0 gate, this yields true D3>0. The result does NOT
postulate the nonzero fourth coefficient or the third-mode rank.

Conversely, if the full Ward-normalized residual is affine in the
actual first derivative, the original literal Wilson minor enjoys
a fifth-order bound rather than just fourth-order decay.

No artificial source, interacting-posterior replacement, assumed
nonzero minor, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PQ2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PQ2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PQ2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PQ2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PQ2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Pure real quantitative fact. A nonzero fourth coefficient and
a fifth-order error cannot be cancelled at sufficiently small
positive beta. No assumption on any physical rank is made. -/
theorem p4Q2PQ2_real_nonzero_of_fifthOrderError
    (value coeff K beta : ℝ)
    (hCoeff : coeff ≠ 0) (hK : 0 ≤ K) (hBeta : 0 < beta)
    (hThreshold : beta < ‖coeff‖ / (K + 1))
    (hError : ‖value - beta ^ 4 * coeff‖ ≤ K * beta ^ 5) :
    value ≠ 0 := by
  intro hValue
  have hDen : 0 < K + 1 := by linarith
  have hCoeffBound : K * beta < ‖coeff‖ := by
    have hFull : beta * (K + 1) < ‖coeff‖ :=
      (lt_div_iff₀ hDen).mp hThreshold
    nlinarith [hFull, hBeta]
  have hWeight : 0 < beta ^ 4 := pow_pos hBeta 4
  have hNorm : ‖beta ^ 4 * coeff‖ = beta ^ 4 * ‖coeff‖ := by
    calc
      ‖beta ^ 4 * coeff‖ = ‖beta‖ ^ 4 * ‖coeff‖ := by
        rw [norm_mul, norm_pow]
      _ = beta ^ 4 * ‖coeff‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hBeta)]
  have hUpper : beta ^ 4 * ‖coeff‖ ≤ K * beta ^ 5 := by
    have h0 : ‖beta ^ 4 * coeff‖ ≤ K * beta ^ 5 := by
      simpa [hValue, norm_neg] using hError
    simpa only [hNorm] using h0
  have hStrict : K * beta ^ 5 < beta ^ 4 * ‖coeff‖ := by
    calc
      K * beta ^ 5 = beta ^ 4 * (K * beta) := by ring
      _ < beta ^ 4 * ‖coeff‖ :=
        mul_lt_mul_of_pos_left hCoeffBound hWeight
  exact (not_le_of_gt hStrict) hUpper

section OriginalWilsonFourthWitness
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "C4" => p4Q2PP2_originalFourthCoefficient H
local notation "Minor" => p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H

/-- Any ACTUAL nonzero original Wilson fourth Haar coefficient gives
a nonzero original literal one- and double-Haar three-boundary minor on
a common positive fine-coupling interval at each fixed finite H. -/
theorem p4Q2PQ2_originalNonzeroFourth_gives_literalMinor_smallFine
    (A B C : Cfg) (hCoeff : C4 A B C ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ beta : ℝ, 0 < beta → beta < delta →
        Minor beta A B C ≠ 0 := by
  obtain ⟨K, hK, hRem⟩ :=
    p4Q2PP5_originalLiteralWilsonMinor_fourthCoefficient H A B C
  have hCpos : 0 < ‖C4 A B C‖ := norm_pos_iff.mpr hCoeff
  have hKpos : 0 < K + 1 := by linarith
  have hMpos : 0 < 1 + 2 * ‖M‖ := by positivity
  let delta : ℝ :=
    min 1 (min (1 / (1 + 2 * ‖M‖)) (‖C4 A B C‖ / (K + 1)))
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min
    · norm_num
    · apply lt_min
      · exact div_pos (by norm_num) hMpos
      · exact div_pos hCpos hKpos
  refine ⟨delta, hdelta, ?_⟩
  intro beta hBeta hSmall
  have hOne : delta ≤ 1 := by
    dsimp [delta]
    exact min_le_left _ _
  have hFine : delta ≤ 1 / (1 + 2 * ‖M‖) := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hLeading : delta ≤ ‖C4 A B C‖ / (K + 1) := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hBetaOne : ‖beta‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hBeta)]
    exact (lt_of_lt_of_le hSmall hOne).le
  have hBudget : ‖beta * (2 * M)‖ ≤ 1 := by
    have hFineBeta : beta < 1 / (1 + 2 * ‖M‖) :=
      lt_of_lt_of_le hSmall hFine
    have hFineProd : beta * (1 + 2 * ‖M‖) < 1 :=
      (lt_div_iff₀ hMpos).mp hFineBeta
    have hNormBudget : ‖beta * (2 * M)‖ = beta * (2 * ‖M‖) := by
      rw [norm_mul, norm_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hBeta)]
    rw [hNormBudget]
    nlinarith [hFineProd, hBeta]
  have hError := hRem beta hBetaOne hBudget
  have hThreshold : beta < ‖C4 A B C‖ / (K + 1) :=
    lt_of_lt_of_le hSmall hLeading
  exact p4Q2PQ2_real_nonzero_of_fifthOrderError
    (Minor beta A B C) (C4 A B C) K beta
    hCoeff hK hBeta hThreshold hError

/-- With the already PROVED genuine physical D2>0 gate (PC/PE),
any eventual nonzero original fourth Wilson action coefficient is
SUFFICIENT for the authentic third Hankel D3 to become positive at
all small fine couplings. Rank-three is a CONCLUSION, not an axiom. -/
theorem p4Q2PQ2_originalNonzeroFourth_gives_thirdHankel_smallFine
    (A B C : Cfg) (hCoeff : C4 A B C ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ beta : ℝ, ∀ hbeta : 0 ≤ beta, 0 < beta →
        beta < delta →
        0 < p4Q2PD_originalWilsonTwoMomentDet H beta hbeta →
        0 < p4Q2PD_originalWilsonThirdMomentGap H beta hbeta := by
  obtain ⟨delta, hdelta, hMinor⟩ :=
    p4Q2PQ2_originalNonzeroFourth_gives_literalMinor_smallFine
      H A B C hCoeff
  refine ⟨delta, hdelta, ?_⟩
  intro beta hbeta hpos hsmall hTwo
  exact (p4Q2PJ_originalThirdMoment_pos_iff_exists_literalWilsonKernelMinor
    H beta hbeta hTwo).2 ⟨A, B, C, hMinor beta hpos hsmall⟩

/-- If the authentic Ward residual is affine in the first Wilson
profile, PP5 improves the literal original Wilson minor's decay
from O(beta^4) to O(beta^5) for every fixed configuration triple.
This records the actual obstruction instead of hiding a zero leading
coefficient or postulating nonzero third Krylov rank. -/
theorem p4Q2PQ2_originalAffineResidual_literalMinor_fifthOrder
    (s t : ℝ)
    (hAffine : ∀ X : Cfg,
      p4Q2PQ_originalQuarticWardResidual H X =
        s * p4Q2PK_originalOneSlabFirstActionMoment H X + t)
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖Minor beta A B C‖ ≤ K * ‖beta‖ ^ 5 := by
  obtain ⟨K, hK, hBound⟩ :=
    p4Q2PP5_originalLiteralWilsonMinor_fourthCoefficient H A B C
  have hZero :
      C4 A B C = 0 :=
    p4Q2PQ_originalFourthCoefficient_zero_of_residual_affine
      H s t hAffine A B C
  refine ⟨K, hK, ?_⟩
  intro beta hOne hBudget
  simpa [hZero] using hBound beta hOne hBudget

end OriginalWilsonFourthWitness
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ2_real_nonzero_of_fifthOrderError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ2_originalNonzeroFourth_gives_literalMinor_smallFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ2_originalNonzeroFourth_gives_thirdHankel_smallFine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PQ2_originalAffineResidual_literalMinor_fifthOrder
