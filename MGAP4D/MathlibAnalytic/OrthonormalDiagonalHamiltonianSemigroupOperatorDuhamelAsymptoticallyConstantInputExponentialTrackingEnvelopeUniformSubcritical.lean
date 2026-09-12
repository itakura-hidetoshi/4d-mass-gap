import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcriticalIntegral

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Left Hamiltonian tracking at every positive rate below both the spectral and
forcing rates, with no resonant/non-resonant case distinction. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ ν : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (hνpos : 0 < ν) (hνδ : ν < δ) (hνμ : ν < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E)) (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
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
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
      b a δ hδ t₀ t ht (A - S) G V hG hV0 hV
  have hforcing :=
    intervalIntegral_exp_memory_mul_le_exponential_tail_uniform_subcritical
      δ μ ν C t₀ t ht hνδ hνμ hC (fun s : ℝ => ‖G s‖) hG.norm
      (by
        intro s hs
        simpa [G] using hFC s hs)
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤ Real.exp (-((t - t₀) * ν)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sub_nonneg.mpr ht]
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * ν)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) * ‖A - S‖ +
          (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖G s‖) := by
      simpa [V, S] using hmass
    _ ≤ Real.exp (-((t - t₀) * ν)) * ‖A - S‖ +
          (C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) :=
      add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
      dsimp [S]
      ring

/-- Right Hamiltonian tracking has the same resonance-free subcritical envelope,
without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ ν : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (hνpos : 0 < ν) (hνδ : ν < δ) (hνμ : ν < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E)) (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
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
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
      b a δ hδ t₀ t ht (A - S) G V hG hV0 hV
  have hforcing :=
    intervalIntegral_exp_memory_mul_le_exponential_tail_uniform_subcritical
      δ μ ν C t₀ t ht hνδ hνμ hC (fun s : ℝ => ‖G s‖) hG.norm
      (by
        intro s hs
        simpa [G] using hFC s hs)
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤ Real.exp (-((t - t₀) * ν)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sub_nonneg.mpr ht]
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * ν)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) * ‖A - S‖ +
          (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖G s‖) := by
      simpa [V, S] using hmass
    _ ≤ Real.exp (-((t - t₀) * ν)) * ‖A - S‖ +
          (C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) :=
      add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / (max δ μ - ν)) * Real.exp (-((t - t₀) * ν)) := by
      dsimp [S]
      ring

end

end MathlibAnalytic
end MGAP4D
