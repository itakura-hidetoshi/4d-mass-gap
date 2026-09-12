import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputTracking
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingGain
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingPracticalSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-time tracking gain for left Hamiltonian multiplication when the forcing
stays within `M` of a constant target on the time interval. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_left
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
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let G : ℝ → (E →L[ℝ] E) := fun r => F r - F_lim
  let V : ℝ → (E →L[ℝ] E) := fun r => U r - S
  have hS : orthonormalDiagonalOperator b a * S = F_lim := by
    dsimp [S]
    exact orthonormalDiagonalHamiltonian_leftSteadyState_stationary
      b a δ hδ hδpos F_lim
  have hG : Continuous G := by
    dsimp [G]
    exact hF.sub continuous_const
  have hV0 : V t₀ = A - S := by
    simp [V, hU0]
  have hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r := by
    intro r
    have hconst : HasDerivAt (fun _ : ℝ => S) 0 r :=
      hasDerivAt_const (x := r) (c := S)
    have hsub := (hU r).sub hconst
    have hderiv :
        (-orthonormalDiagonalOperator b a) * U r + F r =
          (-orthonormalDiagonalOperator b a) * (U r - S) +
            (F r - F_lim) := by
      rw [← hS]
      noncomm_ring
    convert hsub using 1 <;> simp [V, G]
    simpa only [neg_mul] using hderiv.symm
  have hbound :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
      b a δ hδ hδpos t₀ t ht (A - S) G V M hG
      (by
        intro s hs
        simpa [G] using hFM s hs)
      hV0 hV
  simpa [V, S] using hbound

/-- Finite-time tracking gain for right Hamiltonian multiplication, without a
commutation hypothesis on the target forcing. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_right
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
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let G : ℝ → (E →L[ℝ] E) := fun r => F r - F_lim
  let V : ℝ → (E →L[ℝ] E) := fun r => U r - S
  have hS : S * orthonormalDiagonalOperator b a = F_lim := by
    dsimp [S]
    exact orthonormalDiagonalHamiltonian_rightSteadyState_stationary
      b a δ hδ hδpos F_lim
  have hG : Continuous G := by
    dsimp [G]
    exact hF.sub continuous_const
  have hV0 : V t₀ = A - S := by
    simp [V, hU0]
  have hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r := by
    intro r
    have hconst : HasDerivAt (fun _ : ℝ => S) 0 r :=
      hasDerivAt_const (x := r) (c := S)
    have hsub := (hU r).sub hconst
    have hderiv :
        U r * (-orthonormalDiagonalOperator b a) + F r =
          (U r - S) * (-orthonormalDiagonalOperator b a) +
            (F r - F_lim) := by
      rw [← hS]
      noncomm_ring
    convert hsub using 1 <;> simp [V, G]
    simpa only [mul_neg] using hderiv.symm
  have hbound :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
      b a δ hδ hδpos t₀ t ht (A - S) G V M hG
      (by
        intro s hs
        simpa [G] using hFM s hs)
      hV0 hV
  simpa [V, S] using hbound

/-- Left tracking is bounded by a decaying initial mismatch plus the static tail
forcing gain `M / δ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_left
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
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
        M / δ := by
  have hgain :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_left
      b a δ hδ hδpos t₀ t ht A F U F_lim M hF hFM hU0 hU
  have hratio :=
    one_sub_exp_neg_mul_div_le_inv δ (t - t₀) hδpos (sub_nonneg.mpr ht)
  have hweighted :
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ M / δ := by
    calc
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ (1 / δ) * M :=
        mul_le_mul_of_nonneg_right hratio hM
      _ = M / δ := by ring
  exact hgain.trans (add_le_add (le_refl _) hweighted)

/-- Right tracking has the same static tail forcing gain. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_right
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
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
        M / δ := by
  have hgain :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_right
      b a δ hδ hδpos t₀ t ht A F U F_lim M hF hFM hU0 hU
  have hratio :=
    one_sub_exp_neg_mul_div_le_inv δ (t - t₀) hδpos (sub_nonneg.mpr ht)
  have hweighted :
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ M / δ := by
    calc
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ (1 / δ) * M :=
        mul_le_mul_of_nonneg_right hratio hM
      _ = M / δ := by ring
  exact hgain.trans (add_le_add (le_refl _) hweighted)

/-- With a uniform future tail bound, left evolution enters the explicit tracking
tube after a logarithmic settling time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_left
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
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ / ε) / δ) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ M / δ + ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  have hwait_nonneg :
      0 ≤ max 0 (Real.log (‖A - S‖ / ε) / δ) := le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S] using show t₀ ≤ t from by linarith
  have hultimate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_left
      b a δ hδ hδpos t₀ t ht₀ A F U F_lim M hM hF
      (by
        intro s hs
        exact hFM s hs.1)
      hU0 hU
  by_cases hA : A - S = 0
  · have hbase : ‖U t - S‖ ≤ M / δ := by
      simpa [S, hA] using hultimate
    exact hbase.trans (le_add_of_nonneg_right hε.le)
  · have hAnorm : 0 < ‖A - S‖ := norm_pos_iff.mpr hA
    have hwait_le : max 0 (Real.log (‖A - S‖ / ε) / δ) ≤ t - t₀ := by
      simpa [S] using show max 0
        (Real.log
          (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ / ε) / δ) ≤
          t - t₀ from by linarith
    have htime : Real.log (‖A - S‖ / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have htransient :
        Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        δ ε ‖A - S‖ (t - t₀) hδpos hε hAnorm htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
          Real.exp (-((t - t₀) * δ)) *
              ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
            M / δ := hultimate
      _ ≤ ε + M / δ := by
        simpa [S] using add_le_add htransient (le_refl (M / δ))
      _ = M / δ + ε := add_comm _ _

/-- Right evolution has the identical practical tracking tube, without a
commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_right
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
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ / ε) / δ) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ M / δ + ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  have hwait_nonneg :
      0 ≤ max 0 (Real.log (‖A - S‖ / ε) / δ) := le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S] using show t₀ ≤ t from by linarith
  have hultimate :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_right
      b a δ hδ hδpos t₀ t ht₀ A F U F_lim M hM hF
      (by
        intro s hs
        exact hFM s hs.1)
      hU0 hU
  by_cases hA : A - S = 0
  · have hbase : ‖U t - S‖ ≤ M / δ := by
      simpa [S, hA] using hultimate
    exact hbase.trans (le_add_of_nonneg_right hε.le)
  · have hAnorm : 0 < ‖A - S‖ := norm_pos_iff.mpr hA
    have hwait_le : max 0 (Real.log (‖A - S‖ / ε) / δ) ≤ t - t₀ := by
      simpa [S] using show max 0
        (Real.log
          (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ / ε) / δ) ≤
          t - t₀ from by linarith
    have htime : Real.log (‖A - S‖ / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have htransient :
        Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        δ ε ‖A - S‖ (t - t₀) hδpos hε hAnorm htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
          Real.exp (-((t - t₀) * δ)) *
              ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
            M / δ := hultimate
      _ ≤ ε + M / δ := by
        simpa [S] using add_le_add htransient (le_refl (M / δ))
      _ = M / δ + ε := add_comm _ _

/-- If the future forcing tail uses half of the error budget, left evolution is
within the full tolerance after an explicit logarithmic tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_tail_settlingTime_left
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
    (hF : Continuous F)
    (ε : ℝ)
    (hε : 0 < ε)
    (hFtail : ∀ s : ℝ, t₀ ≤ s → ‖F s - F_lim‖ ≤ δ * (ε / 2))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ /
              (ε / 2)) / δ) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  have hhalf : 0 < ε / 2 := by linarith
  have hM : 0 ≤ δ * (ε / 2) := mul_nonneg hδpos.le hhalf.le
  have hsettle :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_left
      b a δ hδ hδpos t₀ A F U F_lim (δ * (ε / 2)) hM hF hFtail
      hU0 hU (ε / 2) hhalf t ht
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        (δ * (ε / 2)) / δ + ε / 2 := hsettle
    _ = ε := by
      field_simp [hδpos.ne']
      norm_num

/-- The same half-budget tail condition gives an explicit right tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_tail_settlingTime_right
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
    (hF : Continuous F)
    (ε : ℝ)
    (hε : 0 < ε)
    (hFtail : ∀ s : ℝ, t₀ ≤ s → ‖F s - F_lim‖ ≤ δ * (ε / 2))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ /
              (ε / 2)) / δ) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  have hhalf : 0 < ε / 2 := by linarith
  have hM : 0 ≤ δ * (ε / 2) := mul_nonneg hδpos.le hhalf.le
  have hsettle :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_right
      b a δ hδ hδpos t₀ A F U F_lim (δ * (ε / 2)) hM hF hFtail
      hU0 hU (ε / 2) hhalf t ht
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        (δ * (ε / 2)) / δ + ε / 2 := hsettle
    _ = ε := by
      field_simp [hδpos.ne']
      norm_num

end

end MathlibAnalytic
end MGAP4D
