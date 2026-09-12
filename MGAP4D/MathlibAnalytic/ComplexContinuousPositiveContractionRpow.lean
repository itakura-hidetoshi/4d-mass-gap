import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionNNRpow
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

namespace ComplexContinuousPositiveContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The unital continuous-functional-calculus real power of a complex
continuous linear operator. -/
noncomputable def rpow
    (T : H →L[ℂ] H)
    (x : ℝ) :
    H →L[ℂ] H :=
  CFC.rpow T x

/-- Every unital CFC real power is nonnegative in the Loewner order. -/
theorem rpow_nonneg
    (T : H →L[ℂ] H)
    (x : ℝ) :
    0 ≤ rpow T x := by
  simp [rpow]

/-- Every unital CFC real power is positive in the bundled
`ContinuousLinearMap.IsPositive` sense. -/
theorem rpow_isPositive
    (T : H →L[ℂ] H)
    (x : ℝ) :
    (rpow T x).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive (rpow T x)).1
    (rpow_nonneg T x)

/-- Every unital CFC real power is self-adjoint. -/
theorem rpow_isSelfAdjoint
    (T : H →L[ℂ] H)
    (x : ℝ) :
    IsSelfAdjoint (rpow T x) :=
  (rpow_isPositive T x).isSelfAdjoint

/-- Exponent zero is the identity for the unital CFC real power. -/
@[simp]
theorem rpow_zero
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive) :
    rpow T 0 = 1 := by
  change CFC.rpow T 0 = 1
  exact CFC.rpow_zero T
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- Exponent one recovers a positive operator. -/
theorem rpow_one
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive) :
    rpow T 1 = T := by
  change CFC.rpow T 1 = T
  exact CFC.rpow_one T
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- Natural-number real exponents agree with ordinary natural powers. -/
theorem rpow_natCast
    (T : H →L[ℂ] H)
    (n : ℕ)
    (hpositive : T.IsPositive) :
    rpow T (n : ℝ) = T ^ n := by
  change CFC.rpow T (n : ℝ) = T ^ n
  exact CFC.rpow_natCast T n
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- For a strictly positive nonnegative exponent, the unital real power agrees
with the preceding non-unital nonnegative power. -/
theorem rpow_coe_eq_nnrpow
    (T : H →L[ℂ] H)
    (p : ℝ≥0)
    (hp : 0 < p) :
    rpow T (p : ℝ) = nnrpow T p := by
  unfold rpow nnrpow
  exact (CFC.nnrpow_eq_rpow hp).symm

/-- The real exponent `1 / 2` power is the canonical CFC square root. -/
theorem rpow_one_div_two_eq_squareRoot
    (T : H →L[ℂ] H) :
    rpow T (1 / 2 : ℝ) = squareRoot T := by
  unfold rpow squareRoot
  exact (CFC.sqrt_eq_rpow (a := T)).symm

/-- Real exponents add under multiplication for an invertible operator. -/
theorem rpow_add_of_isUnit
    (T : H →L[ℂ] H)
    (x y : ℝ)
    (hunit : IsUnit T) :
    rpow T (x + y) = rpow T x * rpow T y := by
  unfold rpow
  exact CFC.rpow_add hunit

/-- Iterated unital real powers multiply nonnegative exponents for a positive
operator. -/
theorem rpow_rpow_of_exponent_nonneg
    (T : H →L[ℂ] H)
    (x y : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hpositive : T.IsPositive) :
    rpow (rpow T x) y = rpow T (x * y) := by
  unfold rpow
  exact CFC.rpow_rpow_of_exponent_nonneg T x y hx hy
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- For an exponent in `[0,1]`, the unital CFC real power of an operator below
the identity is again below the identity. -/
theorem rpow_le_one
    (T : H →L[ℂ] H)
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hle : T ≤ 1) :
    rpow T x ≤ 1 := by
  calc
    rpow T x ≤ rpow (1 : H →L[ℂ] H) x := by
      unfold rpow
      exact CFC.rpow_le_rpow
        (A := H →L[ℂ] H) hx hle
    _ = 1 := by
      unfold rpow
      exact CFC.one_rpow

/-- For an exponent in `[0,1]`, the unital CFC real power of an operator in
`[0,I]` again belongs to `[0,I]`. -/
theorem rpow_mem_Icc
    (T : H →L[ℂ] H)
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hle : T ≤ 1) :
    rpow T x ∈ Set.Icc (0 : H →L[ℂ] H) 1 :=
  ⟨rpow_nonneg T x, rpow_le_one T x hx hle⟩

end ComplexContinuousPositiveContraction

end

end MathlibAnalytic
end MGAP4D
