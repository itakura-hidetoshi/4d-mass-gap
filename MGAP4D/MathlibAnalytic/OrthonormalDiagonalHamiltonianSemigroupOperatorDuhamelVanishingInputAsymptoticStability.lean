import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingPracticalSettlingTime
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelZeroInputOperatorStrongConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- For the left operator-valued Hamiltonian equation, any continuous forcing
whose operator norm vanishes at large time produces an operator norm that also
vanishes at large time.

The proof restarts the evolution at a sufficiently late time, bounds the tail
forcing by a small constant, and applies the practical settling-time theorem. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun t =>
      lt_of_lt_of_le hc (norm_nonneg (U t))
  · intro c hc
    let η : ℝ := c / 4
    let M : ℝ := η * δ
    have hη : 0 < η := by
      dsimp [η]
      linarith
    have hM : 0 < M := by
      exact mul_pos hη hδpos
    have hFsmall : ∀ᶠ s : ℝ in atTop, ‖F s‖ < M :=
      hF0.eventually_lt_const hM
    rcases (eventually_atTop.1 hFsmall) with ⟨T, hT⟩
    have hsettle :=
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_left
        b a δ hδ hδpos T (U T) F U M hM.le hF
        (by
          intro s hs
          exact (hT s hs).le)
        rfl hU η hη
    have hthreshold :
        ∀ᶠ t : ℝ in atTop,
          T + max 0 (Real.log (‖U T‖ / η) / δ) ≤ t :=
      eventually_ge_atTop _
    filter_upwards [hthreshold] with t ht
    have hbound : ‖U t‖ ≤ M / δ + η := hsettle t ht
    have hMdiv : M / δ = η := by
      dsimp [M]
      field_simp [hδpos.ne']
    calc
      ‖U t‖ ≤ M / δ + η := hbound
      _ = η + η := by rw [hMdiv]
      _ < c := by
        dsimp [η]
        linarith

/-- The right operator-valued Hamiltonian equation has the same vanishing-input
operator-norm stability, without a Hamiltonian-commutation assumption. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun t =>
      lt_of_lt_of_le hc (norm_nonneg (U t))
  · intro c hc
    let η : ℝ := c / 4
    let M : ℝ := η * δ
    have hη : 0 < η := by
      dsimp [η]
      linarith
    have hM : 0 < M := by
      exact mul_pos hη hδpos
    have hFsmall : ∀ᶠ s : ℝ in atTop, ‖F s‖ < M :=
      hF0.eventually_lt_const hM
    rcases (eventually_atTop.1 hFsmall) with ⟨T, hT⟩
    have hsettle :=
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_right
        b a δ hδ hδpos T (U T) F U M hM.le hF
        (by
          intro s hs
          exact (hT s hs).le)
        rfl hU η hη
    have hthreshold :
        ∀ᶠ t : ℝ in atTop,
          T + max 0 (Real.log (‖U T‖ / η) / δ) ≤ t :=
      eventually_ge_atTop _
    filter_upwards [hthreshold] with t ht
    have hbound : ‖U t‖ ≤ M / δ + η := hsettle t ht
    have hMdiv : M / δ = η := by
      dsimp [M]
      field_simp [hδpos.ne']
    calc
      ‖U t‖ ≤ M / δ + η := hbound
      _ = η + η := by rw [hMdiv]
      _ < c := by
        dsimp [η]
        linarith

/-- Left vanishing-input evolution converges to zero in continuous-linear-map
operator space. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Tendsto U atTop (nhds 0) := by
  exact tendsto_zero_of_tendsto_norm_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      b a δ hδ hδpos F U hF hF0 hU)

/-- Right vanishing-input evolution converges to zero in operator space. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Tendsto U atTop (nhds 0) := by
  exact tendsto_zero_of_tendsto_norm_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      b a δ hδ hδpos F U hF hF0 hU)

/-- Left vanishing-input evolution converges strongly to zero on every fixed
state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_left
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
      b a δ hδ hδpos F U hF hF0 hU) x

/-- Right vanishing-input evolution converges strongly to zero on every fixed
state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_right
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
      b a δ hδ hδpos F U hF hF0 hU) x

/-- Left vanishing-input evolution converges uniformly to zero on the closed unit
ball. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_left
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop, ∀ x : E, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
      b a δ hδ hδpos F U hF hF0 hU)

/-- Right vanishing-input evolution converges uniformly to zero on the closed unit
ball. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_right
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
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop, ∀ x : E, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
      b a δ hδ hδpos F U hF hF0 hU)

end

end MathlibAnalytic
end MGAP4D
