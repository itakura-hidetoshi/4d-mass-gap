import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorArbitraryInitialValueIVPUniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

private noncomputable def operatorLeftMul
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := fun B => A * B
      map_add' := by
        intro B C
        ext x
        simp
      map_smul' := by
        intro c B
        ext x
        simp }
    ‖A‖
    (fun B => norm_mul_le A B)

private noncomputable def operatorRightMul
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := fun B => B * A
      map_add' := by
        intro B C
        ext x
        simp
      map_smul' := by
        intro c B
        ext x
        simp }
    ‖A‖
    (fun B => by
      simpa [mul_comm] using norm_mul_le B A)

/-- Operator-valued variation of constants for the left finite real diagonal
Hamiltonian equation. For continuous forcing `F`, every operator-norm solution
of `U' = -H U + F`, `U t₀ = A`, is
`S (t - t₀) A + ∫ s in t₀..t, S (t - s) F s`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator b a) * U t + F t) t) :
    U = fun t : ℝ =>
      orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) * A +
        ∫ s in t₀..t,
          orthonormalDiagonalHamiltonianSemigroup b a (t - s) * F s := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)))
        (H * S (-(s - t₀))) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
        b a (-(s - t₀))).scomp s (((hasDerivAt_id' s).sub_const t₀).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)) * U r)
        (S (-(s - t₀)) * F s) s := by
    convert (hSneg s).mul (hU s) using 1
    rw [orthonormalDiagonalHamiltonianSemigroup_commutes_hamiltonian_explicit
      b a (-(s - t₀))]
    noncomm_ring
  have hSnegDiff : Differentiable ℝ (fun r : ℝ => S (-(r - t₀))) :=
    fun s => (hSneg s).differentiableAt
  have hforcingContinuous :
      Continuous (fun s : ℝ => S (-(s - t₀)) * F s) :=
    hSnegDiff.continuous.mul hF
  have hforcingIntegrable :
      IntervalIntegrable (fun s : ℝ => S (-(s - t₀)) * F s) volume t₀ t :=
    hforcingContinuous.intervalIntegrable t₀ t
  have hftc :
      (∫ s in t₀..t, S (-(s - t₀)) * F s) =
        S (-(t - t₀)) * U t - A := by
    simpa [S, hU0] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := t₀) (b := t)
        (f := fun r : ℝ => S (-(r - t₀)) * U r)
        (f' := fun r : ℝ => S (-(r - t₀)) * F r)
        (fun r _ => hprod r) hforcingIntegrable)
  let L := operatorLeftMul (S (t - t₀))
  have hpush :
      S (t - t₀) * (∫ s in t₀..t, S (-(s - t₀)) * F s) =
        ∫ s in t₀..t, S (t - s) * F s := by
    change L (∫ s in t₀..t, S (-(s - t₀)) * F s) = _
    rw [← L.intervalIntegral_comp_comm hforcingIntegrable]
    apply intervalIntegral.integral_congr
    intro s _
    change (S (t - t₀) * S (-(s - t₀))) * F s = S (t - s) * F s
    rw [← orthonormalDiagonalHamiltonianSemigroup_add
      b a (t - t₀) (-(s - t₀))]
    congr 2
    ring
  have hrecover :
      S (t - t₀) * (S (-(t - t₀)) * U t) = U t := by
    rw [← mul_assoc, ← orthonormalDiagonalHamiltonianSemigroup_add
      b a (t - t₀) (-(t - t₀))]
    simp
  have hrelation :
      (∫ s in t₀..t, S (t - s) * F s) =
        U t - S (t - t₀) * A := by
    calc
      (∫ s in t₀..t, S (t - s) * F s) =
          S (t - t₀) * (∫ s in t₀..t, S (-(s - t₀)) * F s) := hpush.symm
      _ = S (t - t₀) * (S (-(t - t₀)) * U t - A) := by rw [hftc]
      _ = U t - S (t - t₀) * A := by rw [mul_sub, hrecover]
  calc
    U t = S (t - t₀) * A + (U t - S (t - t₀) * A) := by abel
    _ = S (t - t₀) * A + ∫ s in t₀..t, S (t - s) * F s := by rw [← hrelation]
    _ = orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) * A +
        ∫ s in t₀..t,
          orthonormalDiagonalHamiltonianSemigroup b a (t - s) * F s := rfl

/-- Operator-valued variation of constants for the right finite real diagonal
Hamiltonian equation. For continuous forcing `F`, every operator-norm solution
of `U' = U (-H) + F`, `U t₀ = A`, is
`A S (t - t₀) + ∫ s in t₀..t, F s S (t - s)`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-orthonormalDiagonalOperator b a) + F t) t) :
    U = fun t : ℝ =>
      A * orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) +
        ∫ s in t₀..t,
          F s * orthonormalDiagonalHamiltonianSemigroup b a (t - s) := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)))
        (H * S (-(s - t₀))) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
        b a (-(s - t₀))).scomp s (((hasDerivAt_id' s).sub_const t₀).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => U r * S (-(r - t₀)))
        (F s * S (-(s - t₀))) s := by
    convert (hU s).mul (hSneg s) using 1
    noncomm_ring
  have hSnegDiff : Differentiable ℝ (fun r : ℝ => S (-(r - t₀))) :=
    fun s => (hSneg s).differentiableAt
  have hforcingContinuous :
      Continuous (fun s : ℝ => F s * S (-(s - t₀))) :=
    hF.mul hSnegDiff.continuous
  have hforcingIntegrable :
      IntervalIntegrable (fun s : ℝ => F s * S (-(s - t₀))) volume t₀ t :=
    hforcingContinuous.intervalIntegrable t₀ t
  have hftc :
      (∫ s in t₀..t, F s * S (-(s - t₀))) =
        U t * S (-(t - t₀)) - A := by
    simpa [S, hU0] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := t₀) (b := t)
        (f := fun r : ℝ => U r * S (-(r - t₀)))
        (f' := fun r : ℝ => F r * S (-(r - t₀)))
        (fun r _ => hprod r) hforcingIntegrable)
  let R := operatorRightMul (S (t - t₀))
  have hpush :
      (∫ s in t₀..t, F s * S (-(s - t₀))) * S (t - t₀) =
        ∫ s in t₀..t, F s * S (t - s) := by
    change R (∫ s in t₀..t, F s * S (-(s - t₀))) = _
    rw [← R.intervalIntegral_comp_comm hforcingIntegrable]
    apply intervalIntegral.integral_congr
    intro s _
    change (F s * S (-(s - t₀))) * S (t - t₀) = F s * S (t - s)
    rw [mul_assoc, ← orthonormalDiagonalHamiltonianSemigroup_add
      b a (-(s - t₀)) (t - t₀)]
    congr 2
    ring
  have hrecover :
      (U t * S (-(t - t₀))) * S (t - t₀) = U t := by
    rw [mul_assoc, ← orthonormalDiagonalHamiltonianSemigroup_add
      b a (-(t - t₀)) (t - t₀)]
    simp
  have hrelation :
      (∫ s in t₀..t, F s * S (t - s)) =
        U t - A * S (t - t₀) := by
    calc
      (∫ s in t₀..t, F s * S (t - s)) =
          (∫ s in t₀..t, F s * S (-(s - t₀))) * S (t - t₀) := hpush.symm
      _ = (U t * S (-(t - t₀)) - A) * S (t - t₀) := by rw [hftc]
      _ = U t - A * S (t - t₀) := by rw [sub_mul, hrecover]
  calc
    U t = A * S (t - t₀) + (U t - A * S (t - t₀)) := by abel
    _ = A * S (t - t₀) + ∫ s in t₀..t, F s * S (t - s) := by rw [← hrelation]
    _ = A * orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) +
        ∫ s in t₀..t,
          F s * orthonormalDiagonalHamiltonianSemigroup b a (t - s) := rfl

end

end MathlibAnalytic
end MGAP4D
