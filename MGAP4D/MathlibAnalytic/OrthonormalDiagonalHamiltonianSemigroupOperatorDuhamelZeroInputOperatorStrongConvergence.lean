import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelZeroInputNormConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- Convergence of the norm to zero implies convergence to zero in the ambient
seminormed additive group. -/
theorem tendsto_zero_of_tendsto_norm_zero
    {α X : Type*}
    [SeminormedAddCommGroup X]
    {l : Filter α}
    {f : α → X}
    (h : Tendsto (fun a => ‖f a‖) l (nhds 0)) :
    Tendsto f l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall :
      ∀ᶠ a in l, dist (‖f a‖) 0 < ε :=
    (Metric.tendsto_nhds.1 h) ε hε
  filter_upwards [hsmall] with a ha
  simpa [dist_eq_norm] using ha

/-- Operator-space convergence to zero implies statewise strong convergence for
every fixed vector. -/
theorem continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    {α E F : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {l : Filter α}
    {U : α → (E →L[ℝ] F)}
    (hU : Tendsto U l (nhds 0))
    (x : E) :
    Tendsto (fun a => U a x) l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_cases hx : x = 0
  · exact Filter.Eventually.of_forall fun a => by
      simp [hx, hε]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsmall :
        ∀ᶠ a in l, dist (U a) 0 < ε / ‖x‖ :=
      (Metric.tendsto_nhds.1 hU) (ε / ‖x‖) (div_pos hε hxpos)
    filter_upwards [hsmall] with a ha
    have hop : ‖U a‖ < ε / ‖x‖ := by
      simpa [dist_eq_norm] using ha
    have hmul : ‖U a‖ * ‖x‖ < ε := by
      exact (lt_div_iff₀ hxpos).mp hop
    have happ : ‖U a x‖ < ε :=
      lt_of_le_of_lt ((U a).le_opNorm x) hmul
    simpa [dist_eq_norm] using happ

/-- Operator-space convergence to zero is uniform on the closed unit ball. -/
theorem continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
    {α E F : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {l : Filter α}
    {U : α → (E →L[ℝ] F)}
    (hU : Tendsto U l (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ a in l, ∀ x : E, ‖x‖ ≤ 1 → ‖U a x‖ < ε := by
  intro ε hε
  have hsmall :
      ∀ᶠ a in l, dist (U a) 0 < ε :=
    (Metric.tendsto_nhds.1 hU) ε hε
  filter_upwards [hsmall] with a ha
  intro x hx
  have hop : ‖U a‖ < ε := by
    simpa [dist_eq_norm] using ha
  calc
    ‖U a x‖ ≤ ‖U a‖ * ‖x‖ := (U a).le_opNorm x
    _ ≤ ‖U a‖ * 1 :=
      mul_le_mul_of_nonneg_left hx (norm_nonneg (U a))
    _ = ‖U a‖ := mul_one _
    _ < ε := hop

/-- Left zero-input Hamiltonian evolution converges to zero in the continuous
linear-operator space. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_left
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
    Tendsto U atTop (nhds 0) := by
  exact
    tendsto_zero_of_tendsto_norm_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_left
        b a δ hδ hδpos t₀ A U hU0 hU)

/-- Right zero-input Hamiltonian evolution converges to zero in operator space,
without a commutation hypothesis on the initial operator. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_right
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
    Tendsto U atTop (nhds 0) := by
  exact
    tendsto_zero_of_tendsto_norm_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_right
        b a δ hδ hδpos t₀ A U hU0 hU)

/-- Left zero-input evolution converges strongly to zero on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_apply_zero_left
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
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact
    continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_left
        b a δ hδ hδpos t₀ A U hU0 hU) x

/-- Right zero-input evolution converges strongly to zero on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_apply_zero_right
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
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact
    continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_right
        b a δ hδ hδpos t₀ A U hU0 hU) x

/-- Left zero-input evolution converges uniformly to zero on the closed unit ball. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_eventually_uniform_unitBall_zero_left
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
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop, ∀ x : E, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_left
        b a δ hδ hδpos t₀ A U hU0 hU)

/-- Right zero-input evolution converges uniformly to zero on the closed unit ball. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_eventually_uniform_unitBall_zero_right
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
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop, ∀ x : E, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_right
        b a δ hδ hδpos t₀ A U hU0 hU)

end

end MathlibAnalytic
end MGAP4D
