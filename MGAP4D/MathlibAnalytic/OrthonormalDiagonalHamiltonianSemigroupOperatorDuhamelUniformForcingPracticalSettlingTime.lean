import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingGain
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelZeroInputSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Under a uniformly bounded future forcing term, left operator-valued
Hamiltonian evolution enters the explicit ultimate ball after the logarithmic
settling time and remains there. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_left
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
    (F U : ℝ → (E →L[ℝ] E))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A‖ / ε) / δ) ≤ t →
        ‖U t‖ ≤ M / δ + ε := by
  intro t ht
  have hwait_nonneg : 0 ≤ max 0 (Real.log (‖A‖ / ε) / δ) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have hultimate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
      b a δ hδ hδpos t₀ t ht₀ A F U M hM hF
      (by
        intro s hs
        exact hFM s hs.1)
      hU0 hU
  by_cases hA : A = 0
  · have hbase : ‖U t‖ ≤ M / δ := by
      simpa [hA] using hultimate
    exact hbase.trans (le_add_of_nonneg_right hε.le)
  · have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hwait_le : max 0 (Real.log (‖A‖ / ε) / δ) ≤ t - t₀ := by
      linarith
    have htime : Real.log (‖A‖ / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have htransient :
        Real.exp (-((t - t₀) * δ)) * ‖A‖ ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        δ ε ‖A‖ (t - t₀) hδpos hε hAnorm htime
    calc
      ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ + M / δ := hultimate
      _ ≤ ε + M / δ := add_le_add_right htransient _
      _ = M / δ + ε := add_comm _ _

/-- Under the same uniformly bounded future forcing term, right operator-valued
Hamiltonian evolution has the identical practical settling-time guarantee,
without a Hamiltonian-commutation assumption on the initial operator. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_right
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
    (F U : ℝ → (E →L[ℝ] E))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A‖ / ε) / δ) ≤ t →
        ‖U t‖ ≤ M / δ + ε := by
  intro t ht
  have hwait_nonneg : 0 ≤ max 0 (Real.log (‖A‖ / ε) / δ) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have hultimate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
      b a δ hδ hδpos t₀ t ht₀ A F U M hM hF
      (by
        intro s hs
        exact hFM s hs.1)
      hU0 hU
  by_cases hA : A = 0
  · have hbase : ‖U t‖ ≤ M / δ := by
      simpa [hA] using hultimate
    exact hbase.trans (le_add_of_nonneg_right hε.le)
  · have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hwait_le : max 0 (Real.log (‖A‖ / ε) / δ) ≤ t - t₀ := by
      linarith
    have htime : Real.log (‖A‖ / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have htransient :
        Real.exp (-((t - t₀) * δ)) * ‖A‖ ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        δ ε ‖A‖ (t - t₀) hδpos hε hAnorm htime
    calc
      ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ + M / δ := hultimate
      _ ≤ ε + M / δ := add_le_add_right htransient _
      _ = M / δ + ε := add_comm _ _

end

end MathlibAnalytic
end MGAP4D
