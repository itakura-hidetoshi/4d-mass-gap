import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingCoordinateMismatch
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingKantorovichWeakDuality
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingTotalVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealProbabilityData

variable {G : Type} [DecidableEq G] [Fintype G]

/-- Indicator of the positive part of the pointwise probability difference. -/
def positiveDifferenceIndicator
    (P Q : FiniteRealProbabilityData G)
    (x : G) : ℝ :=
  if Q.probability x ≤ P.probability x then 1 else 0

/-- The expectation difference of the positive-difference indicator is exactly
the standard half-`L¹` total-variation distance. -/
theorem positiveDifferenceIndicator_expectation_sub_eq_totalVariationDistance
    (P Q : FiniteRealProbabilityData G) :
    P.expectation (P.positiveDifferenceIndicator Q) -
        Q.expectation (P.positiveDifferenceIndicator Q) =
      P.totalVariationDistance Q := by
  classical
  have hPoint (x : G) :
      |P.probability x - Q.probability x| =
        2 * ((P.probability x - Q.probability x) *
          P.positiveDifferenceIndicator Q x) -
          (P.probability x - Q.probability x) := by
    by_cases h : Q.probability x ≤ P.probability x
    · simp [positiveDifferenceIndicator, h,
        abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · have hlt : P.probability x < Q.probability x := lt_of_not_ge h
      simp [positiveDifferenceIndicator, h,
        abs_of_neg (sub_neg.mpr hlt)]
      ring
  have hDifferenceSum :
      (∑ x : G, (P.probability x - Q.probability x)) = 0 := by
    rw [Finset.sum_sub_distrib,
      P.probability_sum_eq_one, Q.probability_sum_eq_one]
    ring
  have hL1 :
      P.l1Distance Q =
        2 * ∑ x : G,
          (P.probability x - Q.probability x) *
            P.positiveDifferenceIndicator Q x := by
    unfold l1Distance
    calc
      (∑ x : G, |P.probability x - Q.probability x|) =
          ∑ x : G,
            (2 * ((P.probability x - Q.probability x) *
              P.positiveDifferenceIndicator Q x) -
              (P.probability x - Q.probability x)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hPoint x
      _ = 2 * ∑ x : G,
            (P.probability x - Q.probability x) *
              P.positiveDifferenceIndicator Q x -
          ∑ x : G, (P.probability x - Q.probability x) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ x : G,
            (P.probability x - Q.probability x) *
              P.positiveDifferenceIndicator Q x := by
        rw [hDifferenceSum]
        ring
  have hExpectation :
      P.expectation (P.positiveDifferenceIndicator Q) -
          Q.expectation (P.positiveDifferenceIndicator Q) =
        ∑ x : G,
          (P.probability x - Q.probability x) *
            P.positiveDifferenceIndicator Q x := by
    unfold expectation
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  unfold totalVariationDistance
  rw [hL1, hExpectation]
  ring

variable {ι A : Type}
variable [DecidableEq ι] [Fintype ι]
variable [DecidableEq A] [Fintype A]

/-- The positive-difference indicator of two product laws is Hamming
`1`-Lipschitz.  This is the finite zero-one test realizing total variation
inside the Hamming dual class. -/
theorem positiveDifferenceIndicator_hammingOneLipschitz
    (P Q : FiniteRealProbabilityData (ι → A)) :
    FiniteProductHammingOneLipschitz
      (P.positiveDifferenceIndicator Q) := by
  intro left right
  by_cases hEq : left = right
  · subst right
    simp
  · have hAbs :
        |P.positiveDifferenceIndicator Q left -
          P.positiveDifferenceIndicator Q right| ≤ 1 := by
      unfold positiveDifferenceIndicator
      split_ifs <;> norm_num
    have hOne :
        (1 : ℝ) ≤ finiteProductHammingDistanceReal left right := by
      have h :=
        finiteDiscreteDisagreementCost_le_finiteProductHammingDistanceReal
          left right
      simpa [finiteDiscreteDisagreementCost, hEq] using h
    exact hAbs.trans hOne

/-- Any Hamming dual bound controls the standard total-variation distance. -/
theorem HammingDualBound.totalVariationDistance_le
    {P Q : FiniteRealProbabilityData (ι → A)}
    {bound : ℝ}
    (hBound : P.HammingDualBound Q bound) :
    P.totalVariationDistance Q ≤ bound := by
  have h := hBound
    (P.positiveDifferenceIndicator Q)
    (P.positiveDifferenceIndicator_hammingOneLipschitz Q)
  rw [P.positiveDifferenceIndicator_expectation_sub_eq_totalVariationDistance Q]
    at h
  simpa [abs_of_nonneg (P.totalVariationDistance_nonneg Q)] using h

end FiniteRealProbabilityData

/-- One displayed-coordinate mismatch is bounded by complete-state discrete
disagreement. -/
theorem finiteProductMismatchIndicator_le_finiteDiscreteDisagreementCost
    {ι A : Type}
    [DecidableEq A]
    (left right : ι → A)
    (source : ι) :
    finiteProductMismatchIndicator left right source ≤
      finiteDiscreteDisagreementCost left right := by
  by_cases hCoordinate : left source = right source
  · simp [finiteProductMismatchIndicator, hCoordinate,
      finiteDiscreteDisagreementCost]
  · have hConfiguration : left ≠ right := by
      intro hEq
      exact hCoordinate (congrFun hEq source)
    simp [finiteProductMismatchIndicator, hCoordinate,
      finiteDiscreteDisagreementCost, hConfiguration]

namespace FiniteRealCouplingData

variable {ι A : Type}
variable [DecidableEq ι] [Fintype ι]
variable [DecidableEq A] [Fintype A]
variable {P Q : FiniteRealProbabilityData (ι → A)}

/-- Expected mismatch at one coordinate is bounded by the coupling's complete
configuration disagreement mass. -/
theorem expectedFiniteProductCoordinateMismatch_le_disagreementMass
    (C : FiniteRealCouplingData P Q)
    (source : ι) :
    C.expectedFiniteProductCoordinateMismatch source ≤
      C.disagreementMass := by
  rw [← C.expectedCost_finiteDiscreteDisagreementCost_eq_disagreementMass]
  unfold expectedFiniteProductCoordinateMismatch expectedCost
  apply Finset.sum_le_sum
  intro left _hleft
  apply Finset.sum_le_sum
  intro right _hright
  exact mul_le_mul_of_nonneg_left
    (finiteProductMismatchIndicator_le_finiteDiscreteDisagreementCost
      left right source)
    (C.joint_nonneg left right)

end FiniteRealCouplingData

namespace FiniteRealProbabilityData

variable {ι A : Type}
variable [DecidableEq ι] [Fintype ι]
variable [DecidableEq A] [Fintype A]

/-- A Hamming dual bound for two product laws controls every displayed
coordinate mismatch under their canonical full-state overlap coupling. -/
theorem overlapCouplingData_expectedFiniteProductCoordinateMismatch_le_of_hammingDualBound
    (P Q : FiniteRealProbabilityData (ι → A))
    {bound : ℝ}
    (hBound : P.HammingDualBound Q bound)
    (source : ι) :
    (P.overlapCouplingData Q).expectedFiniteProductCoordinateMismatch source ≤
      bound := by
  calc
    (P.overlapCouplingData Q).expectedFiniteProductCoordinateMismatch source ≤
        (P.overlapCouplingData Q).disagreementMass :=
      (P.overlapCouplingData Q).expectedFiniteProductCoordinateMismatch_le_disagreementMass
        source
    _ = P.totalVariationDistance Q := by
      simpa [totalVariationDistance] using
        P.overlapCouplingData_disagreementMass_eq_half_mul_l1Distance Q
    _ ≤ bound := hBound.totalVariationDistance_le

end FiniteRealProbabilityData

end

end MathlibAnalytic
end MGAP4D
