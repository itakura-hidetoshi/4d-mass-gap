import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionSquareRoot
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder NNReal

namespace ComplexContinuousPositiveContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The non-unital continuous-functional-calculus nonnegative power of a
complex continuous linear operator. At exponent zero this follows Mathlib's
`CFC.nnrpow` convention and equals zero. -/
noncomputable def nnrpow
    (T : H →L[ℂ] H)
    (p : ℝ≥0) :
    H →L[ℂ] H :=
  CFC.nnrpow T p

/-- Every CFC nonnegative power is nonnegative in the Loewner order. -/
theorem nnrpow_nonneg
    (T : H →L[ℂ] H)
    (p : ℝ≥0) :
    0 ≤ nnrpow T p := by
  simpa [nnrpow] using
    (CFC.nnrpow_nonneg (a := T) (x := p))

/-- Every CFC nonnegative power is positive in the bundled
`ContinuousLinearMap.IsPositive` sense. -/
theorem nnrpow_isPositive
    (T : H →L[ℂ] H)
    (p : ℝ≥0) :
    (nnrpow T p).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive (nnrpow T p)).1
    (nnrpow_nonneg T p)

/-- Every CFC nonnegative power is self-adjoint. -/
theorem nnrpow_isSelfAdjoint
    (T : H →L[ℂ] H)
    (p : ℝ≥0) :
    IsSelfAdjoint (nnrpow T p) :=
  (nnrpow_isPositive T p).isSelfAdjoint

/-- The non-unital CFC convention sends exponent zero to the zero operator. -/
@[simp]
theorem nnrpow_zero
    (T : H →L[ℂ] H) :
    nnrpow T 0 = 0 := by
  simpa [nnrpow] using
    (CFC.nnrpow_zero (A := H →L[ℂ] H) (a := T))

/-- Exponent one recovers a positive operator. -/
theorem nnrpow_one
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive) :
    nnrpow T 1 = T := by
  simpa [nnrpow] using
    CFC.nnrpow_one T
      ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- Positive exponents add under multiplication. -/
theorem nnrpow_add
    (T : H →L[ℂ] H)
    {p q : ℝ≥0}
    (hp : 0 < p)
    (hq : 0 < q) :
    nnrpow T (p + q) = nnrpow T p * nnrpow T q := by
  simpa [nnrpow] using
    (CFC.nnrpow_add (a := T) hp hq)

/-- Iterated CFC nonnegative powers multiply their exponents. -/
theorem nnrpow_nnrpow
    (T : H →L[ℂ] H)
    (p q : ℝ≥0) :
    nnrpow (nnrpow T p) q = nnrpow T (p * q) := by
  simpa [nnrpow] using
    (CFC.nnrpow_nnrpow (a := T) (x := p) (y := q))

/-- The exponent `1 / 2` nonnegative power is the canonical CFC square root. -/
theorem nnrpow_one_div_two_eq_squareRoot
    (T : H →L[ℂ] H) :
    nnrpow T (1 / 2) = squareRoot T := by
  simpa [nnrpow, squareRoot] using
    (CFC.sqrt_eq_nnrpow T).symm

/-- For an exponent in `[0,1]`, the CFC nonnegative power of an operator below
the identity is again below the identity. -/
theorem nnrpow_le_one
    (T : H →L[ℂ] H)
    (p : ℝ≥0)
    (hp : p ∈ Set.Icc (0 : ℝ≥0) 1)
    (hle : T ≤ 1) :
    nnrpow T p ≤ 1 := by
  have hmono :
      nnrpow T p ≤ nnrpow (1 : H →L[ℂ] H) p := by
    simpa [nnrpow] using
      (CFC.nnrpow_le_nnrpow
        (A := H →L[ℂ] H) hp hle)
  refine hmono.trans ?_
  rcases eq_zero_or_pos p with hp0 | hp0
  · subst p
    simp
  · have hconvert :
        CFC.nnrpow (1 : H →L[ℂ] H) p =
          CFC.rpow (1 : H →L[ℂ] H) (p : ℝ) := by
      exact CFC.nnrpow_eq_rpow hp0
    have hone :
        CFC.rpow (1 : H →L[ℂ] H) (p : ℝ) = 1 := by
      exact CFC.one_rpow
    rw [nnrpow, hconvert, hone]

/-- For an exponent in `[0,1]`, the CFC nonnegative power of an operator in
`[0,I]` again belongs to `[0,I]`. -/
theorem nnrpow_mem_Icc
    (T : H →L[ℂ] H)
    (p : ℝ≥0)
    (hp : p ∈ Set.Icc (0 : ℝ≥0) 1)
    (hle : T ≤ 1) :
    nnrpow T p ∈ Set.Icc (0 : H →L[ℂ] H) 1 :=
  ⟨nnrpow_nonneg T p, nnrpow_le_one T p hp hle⟩

end ComplexContinuousPositiveContraction

end

end MathlibAnalytic
end MGAP4D
