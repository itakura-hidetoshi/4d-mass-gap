import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelZeroInputNormConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A logarithmic waiting-time inequality implies the corresponding exponential
threshold estimate. -/
theorem exp_neg_mul_mul_le_of_log_div_div_le
    (δ ε A τ : ℝ)
    (hδ : 0 < δ)
    (hε : 0 < ε)
    (hA : 0 < A)
    (htime : Real.log (A / ε) / δ ≤ τ) :
    Real.exp (-(τ * δ)) * A ≤ ε := by
  have hlogtime : Real.log (A / ε) ≤ τ * δ :=
    (div_le_iff₀ hδ).mp htime
  have hratio : 0 < A / ε := div_pos hA hε
  have hexp :
      Real.exp (-(τ * δ)) ≤ Real.exp (-Real.log (A / ε)) :=
    Real.exp_le_exp.mpr (neg_le_neg hlogtime)
  have hexp' : Real.exp (-(τ * δ)) ≤ ε / A := by
    calc
      Real.exp (-(τ * δ)) ≤ Real.exp (-Real.log (A / ε)) := hexp
      _ = (Real.exp (Real.log (A / ε)))⁻¹ := by
        rw [Real.exp_neg]
      _ = (A / ε)⁻¹ := by
        rw [Real.exp_log hratio]
      _ = ε / A := by
        field_simp [hA.ne', hε.ne']
  calc
    Real.exp (-(τ * δ)) * A ≤ (ε / A) * A :=
      mul_le_mul_of_nonneg_right hexp' (le_of_lt hA)
    _ = ε := by
      field_simp [hA.ne']

/-- Left zero-input evolution obeys the exact exponential operator-norm rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_left
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
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r) r) :
    ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ := by
  have hbound :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
      b a δ hδ hδpos t₀ t ht A
      (fun _ : ℝ => (0 : E →L[ℝ] E)) U 0 le_rfl continuous_const
      (by intro s hs; simp) hU0 (by intro r; simpa using hU r)
  simpa using hbound

/-- Right zero-input evolution has the same exponential operator-norm rate,
without a commutation hypothesis on the initial operator. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_right
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
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a)) r) :
    ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ := by
  have hbound :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
      b a δ hδ hδpos t₀ t ht A
      (fun _ : ℝ => (0 : E →L[ℝ] E)) U 0 le_rfl continuous_const
      (by intro s hs; simp) hU0 (by intro r; simpa using hU r)
  simpa using hbound

/-- After the explicit logarithmic settling time, left zero-input evolution is
inside the prescribed operator-norm tolerance. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_epsilon_after_settlingTime_left
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
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r) r)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t₀ + max 0 (Real.log (‖A‖ / ε) / δ) ≤ t) :
    ‖U t‖ ≤ ε := by
  have hwait_nonneg : 0 ≤ max 0 (Real.log (‖A‖ / ε) / δ) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have hrate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_left
      b a δ hδ hδpos t₀ t ht₀ A U hU0 hU
  by_cases hA : A = 0
  · have hzero : ‖U t‖ ≤ 0 := by
      simpa [hA] using hrate
    exact hzero.trans (le_of_lt hε)
  · have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hwait_le : max 0 (Real.log (‖A‖ / ε) / δ) ≤ t - t₀ := by
      linarith
    have htime : Real.log (‖A‖ / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    exact hrate.trans
      (exp_neg_mul_mul_le_of_log_div_div_le
        δ ε ‖A‖ (t - t₀) hδpos hε hAnorm htime)

/-- After the same explicit settling time, right zero-input evolution is inside
the prescribed operator-norm tolerance. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_epsilon_after_settlingTime_right
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
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a)) r)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t₀ + max 0 (Real.log (‖A‖ / ε) / δ) ≤ t) :
    ‖U t‖ ≤ ε := by
  have hwait_nonneg : 0 ≤ max 0 (Real.log (‖A‖ / ε) / δ) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have hrate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_right
      b a δ hδ hδpos t₀ t ht₀ A U hU0 hU
  by_cases hA : A = 0
  · have hzero : ‖U t‖ ≤ 0 := by
      simpa [hA] using hrate
    exact hzero.trans (le_of_lt hε)
  · have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hwait_le : max 0 (Real.log (‖A‖ / ε) / δ) ≤ t - t₀ := by
      linarith
    have htime : Real.log (‖A‖ / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    exact hrate.trans
      (exp_neg_mul_mul_le_of_log_div_div_le
        δ ε ‖A‖ (t - t₀) hδpos hε hAnorm htime)

end

end MathlibAnalytic
end MGAP4D
