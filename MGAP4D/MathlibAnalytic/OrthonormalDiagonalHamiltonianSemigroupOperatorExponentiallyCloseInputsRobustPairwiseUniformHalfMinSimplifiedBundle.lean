import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two left Hamiltonian trajectories whose inputs approach each other exponentially
    obey the canonical resonance-free robust pairwise envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖U t - V t‖ ≤
      (‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2))) := by
  have hW0 : (fun r : ℝ => U r - V r) t₀ = A - B := by
    simp [hU0, hV0]
  have hQ : Continuous (fun r : ℝ => F r - G r) := hF.sub hG
  have hW : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((-orthonormalDiagonalOperator b a) * (U r - V r) + (F r - G r)) r := by
    intro r
    have hsub := (hU r).sub (hV r)
    convert hsub using 1
    noncomm_ring
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht (A - B)
      (fun r : ℝ => F r - G r) (fun r : ℝ => U r - V r) 0 C hC hQ
      (by
        intro s hs
        simpa using hFG s hs.1)
      hW0 (by intro r; simpa using hW r)
  simpa [orthonormalDiagonalHamiltonian_leftSteadyState] using henv

/-- The right-action robust pairwise envelope is identical and requires no
    commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖U t - V t‖ ≤
      (‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2))) := by
  have hW0 : (fun r : ℝ => U r - V r) t₀ = A - B := by
    simp [hU0, hV0]
  have hQ : Continuous (fun r : ℝ => F r - G r) := hF.sub hG
  have hW : ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((U r - V r) * (-orthonormalDiagonalOperator b a) + (F r - G r)) r := by
    intro r
    have hsub := (hU r).sub (hV r)
    convert hsub using 1
    noncomm_ring
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht (A - B)
      (fun r : ℝ => F r - G r) (fun r : ℝ => U r - V r) 0 C hC hQ
      (by
        intro s hs
        simpa using hFG s hs.1)
      hW0 (by intro r; simpa using hW r)
  simpa [orthonormalDiagonalHamiltonian_rightSteadyState] using henv

/-- Left robust pairwise operator distance reaches every positive tolerance after
    the explicit half-min waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max δ μ) / ε)) /
            (min δ μ / 2)) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hcoeff : 0 ≤ ‖A - B‖ + 2 * C / max δ μ :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  have hνpos : 0 < min δ μ / 2 := div_pos (lt_min hδpos hμpos) (by norm_num)
  have hsettle :=
    realFunction_abs_le_epsilon_after_exponentialBound
      (min δ μ / 2) ε (‖A - B‖ + 2 * C / max δ μ) t₀
      hνpos hε hcoeff (fun t : ℝ => ‖U t - V t‖)
      (by
        intro t ht
        have henv :=
          orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
            b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG
            hU0 hV0 hU hV
        simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using henv)
  intro t ht
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hsettle t ht

/-- Right robust pairwise operator distance has the identical explicit waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max δ μ) / ε)) /
            (min δ μ / 2)) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hcoeff : 0 ≤ ‖A - B‖ + 2 * C / max δ μ :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  have hνpos : 0 < min δ μ / 2 := div_pos (lt_min hδpos hμpos) (by norm_num)
  have hsettle :=
    realFunction_abs_le_epsilon_after_exponentialBound
      (min δ μ / 2) ε (‖A - B‖ + 2 * C / max δ μ) t₀
      hνpos hε hcoeff (fun t : ℝ => ‖U t - V t‖)
      (by
        intro t ht
        have henv :=
          orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
            b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG
            hU0 hV0 hU hV
        simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using henv)
  intro t ht
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hsettle t ht

/-- Left robust pairwise tracking acts pointwise on every vector. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      ((‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG
      hU0 hV0 hU hV
  exact (U t - V t).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right henv (norm_nonneg y))

/-- Right robust pairwise tracking has the identical pointwise estimate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖(U t - V t) y‖ ≤
      ((‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG
      hU0 hV0 hU hV
  exact (U t - V t).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right henv (norm_nonneg y))

/-- Every left matrix element of the pairwise error has the robust half-min envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      ((‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG y
      hU0 hV0 hU hV
  have hinner : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hinner
    _ ≤ ‖x‖ *
        (((‖A - B‖ + 2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = ((‖A - B‖ + 2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by ring

/-- Every right matrix element has the identical robust half-min envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      ((‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG y
      hU0 hV0 hU hV
  have hinner : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hinner
    _ ≤ ‖x‖ *
        (((‖A - B‖ + 2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = ((‖A - B‖ + 2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by ring

/-- Left direct matrix-element differences satisfy the same robust envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      ((‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG x y
      hU0 hV0 hU hV

/-- Right direct matrix-element differences satisfy the identical robust envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      ((‖A - B‖ + 2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG x y
      hU0 hV0 hU hV

/-- Every fixed left matrix-element difference reaches a prescribed tolerance after
    the explicit robust half-min waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖) / ε)) /
              (min δ μ / 2)) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hcoeff : 0 ≤ (‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖ := by
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg (norm_nonneg _)
          (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le))
        (norm_nonneg x))
      (norm_nonneg y)
  refine realFunction_abs_le_epsilon_after_exponentialBound
    (min δ μ / 2) ε
      ((‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖) t₀
      (div_pos (lt_min hδpos hμpos) (by norm_num)) hε hcoeff
      (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y)) ?_
  intro t ht
  have hmatrix :=
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG x y
      hU0 hV0 hU hV
  calc
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        ((‖A - B‖ + 2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := hmatrix
    _ = ((‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖) *
          Real.exp (-((t - t₀) * (min δ μ / 2))) := by ring

/-- Every fixed right matrix-element difference has the identical robust waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖) / ε)) /
              (min δ μ / 2)) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hcoeff : 0 ≤ (‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖ := by
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg (norm_nonneg _)
          (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le))
        (norm_nonneg x))
      (norm_nonneg y)
  refine realFunction_abs_le_epsilon_after_exponentialBound
    (min δ μ / 2) ε
      ((‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖) t₀
      (div_pos (lt_min hδpos hμpos) (by norm_num)) hε hcoeff
      (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y)) ?_
  intro t ht
  have hmatrix :=
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A B F G U V C hC hF hG hFG x y
      hU0 hV0 hU hV
  calc
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        ((‖A - B‖ + 2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := hmatrix
    _ = ((‖A - B‖ + 2 * C / max δ μ) * ‖x‖ * ‖y‖) *
          Real.exp (-((t - t₀) * (min δ μ / 2))) := by ring

/-- A single robust half-min waiting time works uniformly over both closed unit
    balls for left matrix elements. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max δ μ) / ε)) /
            (min δ μ / 2)) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ A B F G U V C hC hF hG hFG
      hU0 hV0 hU hV ε hε t ht)

/-- The right-action unit-ball robust settling time is identical. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max δ μ) / ε)) /
            (min δ μ / 2)) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ A B F G U V C hC hF hG hFG
      hU0 hV0 hU hV ε hε t ht)

end

end MathlibAnalytic
end MGAP4D
