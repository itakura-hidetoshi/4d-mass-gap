import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingLongTimeISS
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- For the left operator-valued Hamiltonian equation with zero input, the
operator norm converges to zero at large real time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  have hupper :
      Tendsto
        (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * ‖A‖)
        atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_exp_neg_sub_mul_atTop_zero t₀ δ hδpos).mul_const ‖A‖
  rw [tendsto_order]
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun t =>
      lt_of_lt_of_le hc (norm_nonneg (U t))
  · intro c hc
    have hupperEventually :
        ∀ᶠ t : ℝ in atTop,
          Real.exp (-((t - t₀) * δ)) * ‖A‖ < c :=
      hupper.eventually_lt_const hc
    filter_upwards [Filter.eventually_ge_atTop t₀, hupperEventually] with t ht hlt
    have hbound :=
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
        b a δ hδ hδpos t₀ t ht A
        (fun _ : ℝ => (0 : E →L[ℝ] E)) U 0 le_rfl continuous_const
        (by intro s hs; simp) hU0 (by intro r; simpa using hU r)
    have hbound' :
        ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ := by
      simpa using hbound
    exact lt_of_le_of_lt hbound' hlt

/-- For the right operator-valued Hamiltonian equation with zero input, the
operator norm has the same convergence to zero, without a commutation
hypothesis on the initial operator. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a)) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  have hupper :
      Tendsto
        (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * ‖A‖)
        atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_exp_neg_sub_mul_atTop_zero t₀ δ hδpos).mul_const ‖A‖
  rw [tendsto_order]
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun t =>
      lt_of_lt_of_le hc (norm_nonneg (U t))
  · intro c hc
    have hupperEventually :
        ∀ᶠ t : ℝ in atTop,
          Real.exp (-((t - t₀) * δ)) * ‖A‖ < c :=
      hupper.eventually_lt_const hc
    filter_upwards [Filter.eventually_ge_atTop t₀, hupperEventually] with t ht hlt
    have hbound :=
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
        b a δ hδ hδpos t₀ t ht A
        (fun _ : ℝ => (0 : E →L[ℝ] E)) U 0 le_rfl continuous_const
        (by intro s hs; simp) hU0 (by intro r; simpa using hU r)
    have hbound' :
        ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ := by
      simpa using hbound
    exact lt_of_le_of_lt hbound' hlt

end

end MathlibAnalytic
end MGAP4D
