import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two left Hamiltonian trajectories driven by the same constant input contract at
    the full spectral-gap rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F_lim) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * δ)) := by
  have hUV0 : (fun r : ℝ => U r - V r) t₀ = A - B := by
    simp [hU0, hV0]
  have hUV : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((-orthonormalDiagonalOperator b a) * (U r - V r)) r := by
    intro r
    have hsub := (hU r).sub (hV r)
    convert hsub using 1
    noncomm_ring
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ t ht (A - B) (fun r : ℝ => U r - V r) 0
      hUV0 (by intro r; simpa using hUV r)
  simpa [orthonormalDiagonalHamiltonian_leftSteadyState] using henv

/-- Two right Hamiltonian trajectories driven by the same constant input have the
    identical full-gap contraction estimate, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * δ)) := by
  have hUV0 : (fun r : ℝ => U r - V r) t₀ = A - B := by
    simp [hU0, hV0]
  have hUV : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((U r - V r) * (-orthonormalDiagonalOperator b a)) r := by
    intro r
    have hsub := (hU r).sub (hV r)
    convert hsub using 1
    noncomm_ring
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ t ht (A - B) (fun r : ℝ => U r - V r) 0
      hUV0 (by intro r; simpa using hUV r)
  simpa [orthonormalDiagonalHamiltonian_rightSteadyState] using henv

end

end MathlibAnalytic
end MGAP4D
