import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- Variation of constants for the finite real diagonal Hamiltonian semigroup.

For continuous forcing `f`, every differentiable solution of
`u' = -H u + f`, `u t₀ = x`, is the Duhamel orbit
`S (t - t₀) x + ∫ s in t₀..t, S (t - s) (f s)`.

The proof applies the inverse-time semigroup as an integrating factor, uses the
Banach-valued fundamental theorem of calculus, and pushes the forward semigroup
through the Bochner interval integral. -/
theorem orthonormalDiagonalHamiltonianSemigroup_duhamel_eq_of_hasDerivAt
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t₀ : ℝ)
    (x : E)
    (f u : ℝ → E)
    (hf : Continuous f)
    (hu0 : u t₀ = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u (-(orthonormalDiagonalOperator b a (u t)) + f t) t) :
    u = fun t : ℝ =>
      orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) x +
        ∫ s in t₀..t,
          orthonormalDiagonalHamiltonianSemigroup b a (t - s) (f s) := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)))
        (S (-(s - t₀)) * H) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_right
        b a (-(s - t₀))).scomp s (((hasDerivAt_id' s).sub_const t₀).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-(r - t₀)) (u r))
        (S (-(s - t₀)) (f s)) s := by
    convert (hSneg s).clm_apply (hu s) using 1
    change S (-(s - t₀)) (f s) =
      S (-(s - t₀)) (H (u s)) +
        S (-(s - t₀)) (-(H (u s)) + f s)
    rw [map_add, map_neg]
    abel
  have hSnegDiff : Differentiable ℝ (fun r : ℝ => S (-(r - t₀))) :=
    fun s => (hSneg s).differentiableAt
  have hforcingContinuous :
      Continuous (fun s : ℝ => S (-(s - t₀)) (f s)) :=
    hSnegDiff.continuous.clm_apply hf
  have hforcingIntegrable :
      IntervalIntegrable (fun s : ℝ => S (-(s - t₀)) (f s)) volume t₀ t :=
    hforcingContinuous.intervalIntegrable t₀ t
  have hftc :
      (∫ s in t₀..t, S (-(s - t₀)) (f s)) =
        S (-(t - t₀)) (u t) - x := by
    simpa [S, hu0] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := t₀) (b := t)
        (f := fun r : ℝ => S (-(r - t₀)) (u r))
        (f' := fun r : ℝ => S (-(r - t₀)) (f r))
        (fun r _ => hprod r) hforcingIntegrable)
  have hpush :
      S (t - t₀) (∫ s in t₀..t, S (-(s - t₀)) (f s)) =
        ∫ s in t₀..t, S (t - s) (f s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (S (t - t₀)) hforcingIntegrable]
    apply intervalIntegral.integral_congr
    intro s _
    change (S (t - t₀) * S (-(s - t₀))) (f s) = S (t - s) (f s)
    rw [← orthonormalDiagonalHamiltonianSemigroup_add
      b a (t - t₀) (-(s - t₀))]
    congr 2
    ring
  have hrecover : S (t - t₀) (S (-(t - t₀)) (u t)) = u t := by
    change (S (t - t₀) * S (-(t - t₀))) (u t) = u t
    rw [← orthonormalDiagonalHamiltonianSemigroup_add
      b a (t - t₀) (-(t - t₀))]
    simp
  have hrelation :
      (∫ s in t₀..t, S (t - s) (f s)) = u t - S (t - t₀) x := by
    calc
      (∫ s in t₀..t, S (t - s) (f s)) =
          S (t - t₀) (∫ s in t₀..t, S (-(s - t₀)) (f s)) := hpush.symm
      _ = S (t - t₀) (S (-(t - t₀)) (u t) - x) := by rw [hftc]
      _ = u t - S (t - t₀) x := by rw [map_sub, hrecover]
  calc
    u t = S (t - t₀) x + (u t - S (t - t₀) x) := by abel
    _ = S (t - t₀) x + ∫ s in t₀..t, S (t - s) (f s) := by rw [← hrelation]
    _ = orthonormalDiagonalHamiltonianSemigroup b a (t - t₀) x +
        ∫ s in t₀..t,
          orthonormalDiagonalHamiltonianSemigroup b a (t - s) (f s) := rfl

end

end MathlibAnalytic
end MGAP4D
