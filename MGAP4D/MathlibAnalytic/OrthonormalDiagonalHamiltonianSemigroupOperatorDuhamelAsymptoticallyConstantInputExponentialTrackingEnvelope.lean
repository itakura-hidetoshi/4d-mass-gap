import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingRate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The non-resonant exponential difference quotient is controlled by the slower
of the two rates, with the spectral-separation constant `|δ - μ|⁻¹`. -/
theorem exp_tail_difference_quotient_mul_le_single_rate
    (δ μ C τ : ℝ)
    (hδμ : δ ≠ μ)
    (hC : 0 ≤ C) :
    ((Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ)) * C ≤
      (C / |δ - μ|) * Real.exp (-(τ * min δ μ)) := by
  rcases lt_or_gt_of_ne hδμ with hδltμ | hμltδ
  · have hdenpos : 0 < μ - δ := sub_pos.mpr hδltμ
    have hdenne : μ - δ ≠ 0 := ne_of_gt hdenpos
    have hrewrite :
        (Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ) =
          (Real.exp (-(τ * δ)) - Real.exp (-(τ * μ))) / (μ - δ) := by
      field_simp [sub_ne_zero.mpr hδμ, hdenne]
      ring
    have hquot :
        (Real.exp (-(τ * δ)) - Real.exp (-(τ * μ))) / (μ - δ) ≤
          Real.exp (-(τ * δ)) / (μ - δ) := by
      apply (div_le_div_iff₀ hdenpos).2
      nlinarith [Real.exp_pos (-(τ * μ))]
    calc
      ((Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ)) * C =
          ((Real.exp (-(τ * δ)) - Real.exp (-(τ * μ))) / (μ - δ)) * C := by
            rw [hrewrite]
      _ ≤ (Real.exp (-(τ * δ)) / (μ - δ)) * C :=
        mul_le_mul_of_nonneg_right hquot hC
      _ = (C / |δ - μ|) * Real.exp (-(τ * min δ μ)) := by
        rw [min_eq_left hδltμ.le, abs_of_neg (sub_neg.mpr hδltμ)]
        ring
  · have hdenpos : 0 < δ - μ := sub_pos.mpr hμltδ
    have hquot :
        (Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ) ≤
          Real.exp (-(τ * μ)) / (δ - μ) := by
      apply (div_le_div_iff₀ hdenpos).2
      nlinarith [Real.exp_pos (-(τ * δ))]
    calc
      ((Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ)) * C ≤
          (Real.exp (-(τ * μ)) / (δ - μ)) * C :=
        mul_le_mul_of_nonneg_right hquot hC
      _ = (C / |δ - μ|) * Real.exp (-(τ * min δ μ)) := by
        rw [min_eq_right hμltδ.le, abs_of_pos hdenpos]
        ring

/-- The resonant linear-exponential term admits the elementary half-rate envelope
`τ exp (-δ τ) ≤ (2 / δ) exp (-(δ / 2) τ)`. -/
theorem mul_exp_tail_le_two_div_mul_exp_half_rate
    (δ τ : ℝ)
    (hδpos : 0 < δ)
    (hτ : 0 ≤ τ) :
    τ * Real.exp (-(τ * δ)) ≤
      (2 / δ) * Real.exp (-(τ * (δ / 2))) := by
  have hhalfpos : 0 < δ / 2 := by linarith
  have hxnonneg : 0 ≤ (δ / 2) * τ :=
    mul_nonneg hhalfpos.le hτ
  have hxle : (δ / 2) * τ ≤ Real.exp ((δ / 2) * τ) := by
    calc
      (δ / 2) * τ ≤ (δ / 2) * τ + 1 := by linarith
      _ ≤ Real.exp ((δ / 2) * τ) := Real.add_one_le_exp _
  have htau : τ ≤ (2 / δ) * Real.exp ((δ / 2) * τ) := by
    rw [show 2 / δ = 1 / (δ / 2) by
      field_simp [hδpos.ne']]
    rw [one_div]
    exact (le_div_iff₀ hhalfpos).2 (by simpa [mul_comm] using hxle)
  have hmul :=
    mul_le_mul_of_nonneg_right htau (Real.exp_pos (-(τ * δ))).le
  calc
    τ * Real.exp (-(τ * δ)) ≤
        ((2 / δ) * Real.exp ((δ / 2) * τ)) * Real.exp (-(τ * δ)) := hmul
    _ = (2 / δ) * Real.exp (-(τ * (δ / 2))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

/-- Non-resonant left tracking is controlled by one exponential with rate
`min δ μ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (hμpos : 0 < μ)
    (hδμ : δ ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / |δ - μ|) *
        Real.exp (-((t - t₀) * min δ μ)) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_left
      b a δ μ hδ hδpos hδμ t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * min δ μ)) := by
    apply Real.exp_le_exp.mpr
    have hmin : min δ μ ≤ δ := min_le_left _ _
    nlinarith
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hforcing :=
    exp_tail_difference_quotient_mul_le_single_rate
      δ μ C (t - t₀) hδμ hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          ((Real.exp (-((t - t₀) * μ)) -
              Real.exp (-((t - t₀) * δ))) / (δ - μ)) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ +
          (C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simp [S]
      ring

/-- Non-resonant right tracking has the same single-rate envelope, without a
commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (hμpos : 0 < μ)
    (hδμ : δ ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / |δ - μ|) *
        Real.exp (-((t - t₀) * min δ μ)) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_right
      b a δ μ hδ hδpos hδμ t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * min δ μ)) := by
    apply Real.exp_le_exp.mpr
    have hmin : min δ μ ≤ δ := min_le_left _ _
    nlinarith
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hforcing :=
    exp_tail_difference_quotient_mul_le_single_rate
      δ μ C (t - t₀) hδμ hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          ((Real.exp (-((t - t₀) * μ)) -
              Real.exp (-((t - t₀) * δ))) / (δ - μ)) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ +
          (C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simp [S]
      ring

/-- The non-resonant left envelope yields an explicit logarithmic tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_nonresonant_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (hμpos : 0 < μ)
    (hδμ : δ ≠ μ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                C / |δ - μ|) / ε) / min δ μ) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let K := ‖A - S‖ + C / |δ - μ|
  have hratepos : 0 < min δ μ := lt_min hδpos hμpos
  have habsnonneg : 0 ≤ |δ - μ| := abs_nonneg _
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _) (div_nonneg hC habsnonneg)
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / min δ μ) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S, K] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_left
      b a δ μ hδ hδpos hμpos hδμ t₀ t ht₀ A F U F_lim C hC hF
      (by
        intro s hs
        exact hFC s hs.1)
      hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by
      simpa [S, K, hK] using henv
    exact (by simpa [S] using hzero.trans hε.le)
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait_le : max 0 (Real.log (K / ε) / min δ μ) ≤ t - t₀ := by
      simpa [S, K] using show max 0
        (Real.log
          ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
              C / |δ - μ|) / ε) / min δ μ) ≤ t - t₀ from by linarith
    have htime : Real.log (K / ε) / min δ μ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have hdecay :
        Real.exp (-((t - t₀) * min δ μ)) * K ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        (min δ μ) ε K (t - t₀) hratepos hε hKpos htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * min δ μ)) := by
        simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

/-- The non-resonant right envelope has the identical explicit tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_nonresonant_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (hμpos : 0 < μ)
    (hδμ : δ ≠ μ)
    (t₀ : ℝ)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                C / |δ - μ|) / ε) / min δ μ) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let K := ‖A - S‖ + C / |δ - μ|
  have hratepos : 0 < min δ μ := lt_min hδpos hμpos
  have habsnonneg : 0 ≤ |δ - μ| := abs_nonneg _
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _) (div_nonneg hC habsnonneg)
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / min δ μ) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S, K] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_right
      b a δ μ hδ hδpos hμpos hδμ t₀ t ht₀ A F U F_lim C hC hF
      (by
        intro s hs
        exact hFC s hs.1)
      hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by
      simpa [S, K, hK] using henv
    exact (by simpa [S] using hzero.trans hε.le)
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait_le : max 0 (Real.log (K / ε) / min δ μ) ≤ t - t₀ := by
      simpa [S, K] using show max 0
        (Real.log
          ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
              C / |δ - μ|) / ε) / min δ μ) ≤ t - t₀ from by linarith
    have htime : Real.log (K / ε) / min δ μ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have hdecay :
        Real.exp (-((t - t₀) * min δ μ)) * K ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        (min δ μ) ε K (t - t₀) hratepos hε hKpos htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * min δ μ)) := by
        simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

/-- Resonant left tracking is controlled by a single exponential with rate `δ / 2`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_resonant_left
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
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / δ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
      b a δ hδ hδpos t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * (δ / 2))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hlinear :=
    mul_exp_tail_le_two_div_mul_exp_half_rate δ (t - t₀) hδpos hτ
  have hforcing :
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C ≤
        ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C :=
    mul_le_mul_of_nonneg_right hlinear hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ +
          ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / δ) * Real.exp (-((t - t₀) * (δ / 2))) := by
      simp [S]
      field_simp [hδpos.ne']
      ring

/-- Resonant right tracking has the same half-rate envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_resonant_right
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
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / δ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
      b a δ hδ hδpos t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * (δ / 2))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hlinear :=
    mul_exp_tail_le_two_div_mul_exp_half_rate δ (t - t₀) hδpos hτ
  have hforcing :
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C ≤
        ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C :=
    mul_le_mul_of_nonneg_right hlinear hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ +
          ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / δ) * Real.exp (-((t - t₀) * (δ / 2))) := by
      simp [S]
      field_simp [hδpos.ne']
      ring

/-- The resonant left half-rate envelope yields an explicit logarithmic tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_resonant_left
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
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / δ) / ε) / (δ / 2)) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let K := ‖A - S‖ + 2 * C / δ
  have hratepos : 0 < δ / 2 := by linarith
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hδpos.le)
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / (δ / 2)) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S, K] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_resonant_left
      b a δ hδ hδpos t₀ t ht₀ A F U F_lim C hC hF
      (by
        intro s hs
        exact hFC s hs.1)
      hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by
      simpa [S, K, hK] using henv
    exact (by simpa [S] using hzero.trans hε.le)
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait_le : max 0 (Real.log (K / ε) / (δ / 2)) ≤ t - t₀ := by
      simpa [S, K] using show max 0
        (Real.log
          ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
              2 * C / δ) / ε) / (δ / 2)) ≤ t - t₀ from by linarith
    have htime : Real.log (K / ε) / (δ / 2) ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have hdecay :
        Real.exp (-((t - t₀) * (δ / 2))) * K ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        (δ / 2) ε K (t - t₀) hratepos hε hKpos htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * (δ / 2))) := by
        simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

/-- The resonant right half-rate envelope has the identical explicit tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_resonant_right
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
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / δ) / ε) / (δ / 2)) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let K := ‖A - S‖ + 2 * C / δ
  have hratepos : 0 < δ / 2 := by linarith
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hδpos.le)
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / (δ / 2)) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S, K] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_resonant_right
      b a δ hδ hδpos t₀ t ht₀ A F U F_lim C hC hF
      (by
        intro s hs
        exact hFC s hs.1)
      hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by
      simpa [S, K, hK] using henv
    exact (by simpa [S] using hzero.trans hε.le)
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait_le : max 0 (Real.log (K / ε) / (δ / 2)) ≤ t - t₀ := by
      simpa [S, K] using show max 0
        (Real.log
          ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
              2 * C / δ) / ε) / (δ / 2)) ≤ t - t₀ from by linarith
    have htime : Real.log (K / ε) / (δ / 2) ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have hdecay :
        Real.exp (-((t - t₀) * (δ / 2))) * K ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        (δ / 2) ε K (t - t₀) hratepos hε hKpos htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * (δ / 2))) := by
        simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

end

end MathlibAnalytic
end MGAP4D
