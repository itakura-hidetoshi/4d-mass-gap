import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalBoundaryLoopCorrectedRankV5_PZ37P
import Mathlib.Tactic

/-!
# PZ37P — quantitative bound for the H=0 original boundary loop obstruction

The original 48 surviving ordered plaquette pairs contribute products of
two true normalized SU(2) fundamental characters. Since the original Wilson
energy lies in [0,2], every factor is bounded by one in absolute value.
Kernel-checked incidence geometry gives 48 pairs: the genuine correction
polynomial is globally bounded by 48, *without* evaluating its value at
each chosen physical boundary.

Bound the original alternating wedge by 96 times the sum of the two spatial
Wilson-action differences. The explicit 0,4,16 Wilson-energy criterion
then dominates the *entire* possible exceptional H=0 correction, forcing
a nonzero seventh coefficient and hence the actual nonzero double-Haar minor.

This establishes a quantitative SU(2) witness criterion, not the yet
unproved existence of a triple with precisely these three action values.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette 0
local notation "Cfg₀" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
local notation "w₀" => p4Q2PS_originalHalfSpatialAction 0
local notation "R₀" => p4Q2PZ37L_originalMinimalBoundaryLoopSum
local notation "W₀" => p4Q2PZ37B_originalBoundaryWedge 0 w₀ R₀

/-- Bounded actual SU(2) character, directly from the original Wilson
energy interval (not a surrogate/finite-group character). -/
theorem p4Q2PZ37P_originalOneLinkCharacter_abs_le_one (g : G) :
    |p4Q2PZ35C_originalOneLinkCharacter g| ≤ 1 := by
  have hLow : 0 ≤ specialUnitaryWilsonPlaquetteEnergy 2 g :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by decide) g
  have hHigh : specialUnitaryWilsonPlaquetteEnergy 2 g ≤ 2 :=
    specialUnitaryWilsonPlaquetteEnergy_le_two (by decide) g
  unfold p4Q2PZ35C_originalOneLinkCharacter
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem p4Q2PZ37P_originalCharacterProduct_abs_le_one (g h : G) :
    |p4Q2PZ35C_originalOneLinkCharacter g *
      p4Q2PZ35C_originalOneLinkCharacter h| ≤ 1 := by
  calc
    |p4Q2PZ35C_originalOneLinkCharacter g *
      p4Q2PZ35C_originalOneLinkCharacter h| =
        |p4Q2PZ35C_originalOneLinkCharacter g| *
          |p4Q2PZ35C_originalOneLinkCharacter h| := abs_mul _ _
    _ ≤ (1 : ℝ) * 1 :=
      mul_le_mul
        (p4Q2PZ37P_originalOneLinkCharacter_abs_le_one g)
        (p4Q2PZ37P_originalOneLinkCharacter_abs_le_one h)
        (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- Each individual *original* H=0 48-pair winding term has absolute
value at most one, including either true geometric orientation. -/
theorem p4Q2PZ37P_originalMinimalBoundaryLoops_abs_le_one
    (p q : Plaq) (B : Cfg₀) :
    |p4Q2PZ37L_originalMinimalBoundaryLoops p q B| ≤ 1 := by
  unfold p4Q2PZ37L_originalMinimalBoundaryLoops
  split_ifs <;> exact p4Q2PZ37P_originalCharacterProduct_abs_le_one _ _

/-- Global bound of the *actual* minimal-period overlap polynomial:
there are 48 (not an arbitrarily estimated number of) ordered pairs. -/
theorem p4Q2PZ37P_originalMinimalBoundaryLoopSum_abs_le_48
    (B : Cfg₀) :
    |R₀ B| ≤ 48 := by
  classical
  let P : Finset (Plaq × Plaq) :=
    p4Q2PZ37J_originalMinimalOverlapPairs
  let F : Plaq × Plaq → ℝ :=
    fun pq => p4Q2PZ37L_originalMinimalBoundaryLoops pq.1 pq.2 B
  have hPcard : P.card = 48 :=
    p4Q2PZ37J_originalMinimalOverlapPairs_card
  have hTerm (pq : Plaq × Plaq) : |F pq| ≤ 1 :=
    p4Q2PZ37P_originalMinimalBoundaryLoops_abs_le_one pq.1 pq.2 B
  have hUpper : (∑ pq ∈ P, F pq) ≤ (P.card : ℝ) := by
    calc
      (∑ pq ∈ P, F pq) ≤ ∑ _pq ∈ P, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro pq hpq
        exact (abs_le.mp (hTerm pq)).2
      _ = (P.card : ℝ) := by simp
  have hLower : -(P.card : ℝ) ≤ (∑ pq ∈ P, F pq) := by
    calc
      -(P.card : ℝ) = ∑ _pq ∈ P, (-1 : ℝ) := by simp
      _ ≤ ∑ pq ∈ P, F pq := by
        apply Finset.sum_le_sum
        intro pq hpq
        exact (abs_le.mp (hTerm pq)).1
  change |∑ pq ∈ P, F pq| ≤ 48
  exact abs_le.mpr
    ⟨by simpa only [hPcard, Nat.cast_ofNat] using hLower,
     by simpa only [hPcard, Nat.cast_ofNat] using hUpper⟩

/-- Bound on the actual exceptional H=0 alternating boundary-loop
response, with no assumption of affine behavior or its vanishing. -/
theorem p4Q2PZ37P_originalMinimalBoundaryWedge_abs_le
    (A B C : Cfg₀) :
    |W₀ A B C| ≤ (|w₀ B - w₀ A| + |w₀ C - w₀ A|) * 96 := by
  have hR (D : Cfg₀) : |R₀ D| ≤ 48 :=
    p4Q2PZ37P_originalMinimalBoundaryLoopSum_abs_le_48 D
  have hRB : |R₀ B - R₀ A| ≤ 96 := by
    calc
      |R₀ B - R₀ A| ≤ |R₀ B| + |R₀ A| := abs_sub_le _ _
      _ ≤ 48 + 48 := add_le_add (hR B) (hR A)
      _ = 96 := by norm_num
  have hRC : |R₀ C - R₀ A| ≤ 96 := by
    calc
      |R₀ C - R₀ A| ≤ |R₀ C| + |R₀ A| := abs_sub_le _ _
      _ ≤ 48 + 48 := add_le_add (hR C) (hR A)
      _ = 96 := by norm_num
  unfold p4Q2PZ37B_originalBoundaryWedge
  calc
    |(w₀ B - w₀ A) * (R₀ C - R₀ A) -
        (w₀ C - w₀ A) * (R₀ B - R₀ A)| ≤
      |(w₀ B - w₀ A) * (R₀ C - R₀ A)| +
        |(w₀ C - w₀ A) * (R₀ B - R₀ A)| := abs_sub_le _ _
    _ = |w₀ B - w₀ A| * |R₀ C - R₀ A| +
          |w₀ C - w₀ A| * |R₀ B - R₀ A| := by rw [abs_mul, abs_mul]
    _ ≤ |w₀ B - w₀ A| * 96 + |w₀ C - w₀ A| * 96 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hRC (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hRB (abs_nonneg _))
    _ = (|w₀ B - w₀ A| + |w₀ C - w₀ A|) * 96 := by ring

/-- Concrete rational dominance: genuine spatial Wilson half-actions
0,4,16 force the corrected seventh coefficient nonzero for *any*
values of the actual SU(2) boundary-loop polynomial. No false
assumption that the exceptional correction vanishes. -/
theorem p4Q2PZ37P_originalMinimalCorrectedCoefficient_nonzero_of_spread
    (A B C : Cfg₀)
    (hA : w₀ A = 0) (hB : w₀ B = 4) (hC : w₀ C = 16) :
    p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient A B C ≠ 0 := by
  let V : ℝ :=
    PZ37VandermondeAlgebra.vandermonde (w₀ A) (w₀ B) (w₀ C)
  let W : ℝ := W₀ A B C
  have hV : V = 768 := by
    dsimp only [V]
    norm_num [PZ37VandermondeAlgebra.vandermonde, hA, hB, hC]
  have hW : |W| ≤ 1920 := by
    simpa only [W, hA, hB, hC, sub_zero, abs_ofNat, Nat.cast_ofNat]
      using (p4Q2PZ37P_originalMinimalBoundaryWedge_abs_le A B C)
  have hCorrBound : |(3/8192 : ℝ) * W| < |V / 512| := by
    have hMult : (3/8192 : ℝ) * |W| ≤ (3/8192) * 1920 :=
      mul_le_mul_of_nonneg_left hW (by norm_num)
    calc
      |(3/8192 : ℝ) * W| = (3/8192) * |W| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3/8192)]
      _ ≤ (3/8192) * 1920 := hMult
      _ < (768 : ℝ) / 512 := by norm_num
      _ = |V / 512| := by rw [hV]; norm_num
  intro hzero
  have hEq : -(V / 512) = (3/8192 : ℝ) * W := by
    have hh :
        -(V)/512 - (3/8192 : ℝ) * W = 0 := by
      simpa only [p4Q2PZ37P_originalMinimalCorrectedSeventhCoefficient, V, W]
        using hzero
    have hs := sub_eq_zero.mp hh
    simpa only [neg_div] using hs
  have hAbsEq : |V / 512| = |(3/8192 : ℝ) * W| := by
    have := congrArg abs hEq
    simpa only [abs_neg] using this
  exact (not_lt_of_ge hAbsEq.le) hCorrBound

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_originalMinimalBoundaryLoopSum_abs_le_48
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_originalMinimalBoundaryWedge_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37P_originalMinimalCorrectedCoefficient_nonzero_of_spread
