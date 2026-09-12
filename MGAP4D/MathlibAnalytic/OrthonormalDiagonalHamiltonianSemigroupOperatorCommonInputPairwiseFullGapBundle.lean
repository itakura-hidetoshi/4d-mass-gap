import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputUnitBallMatrixElementSteadyStateDifferenceFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two left trajectories driven by the same arbitrary input contract at the full gap. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E)) (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * δ)) := by
  have hUV0 : (fun r : ℝ => U r - V r) t₀ = A - B := by simp [hU0, hV0]
  have hUV : ∀ r, HasDerivAt (fun s : ℝ => U s - V s)
      ((-orthonormalDiagonalOperator b a) * (U r - V r)) r := by
    intro r
    have hsub := (hU r).sub (hV r)
    convert hsub using 1
    noncomm_ring
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ t ht (A - B) (fun r => U r - V r) 0 hUV0
      (by intro r; simpa using hUV r)
  simpa [orthonormalDiagonalHamiltonian_leftSteadyState] using henv

/-- Two right trajectories driven by the same arbitrary input contract at the full gap. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E)) (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * δ)) := by
  have hUV0 : (fun r : ℝ => U r - V r) t₀ = A - B := by simp [hU0, hV0]
  have hUV : ∀ r, HasDerivAt (fun s : ℝ => U s - V s)
      ((U r - V r) * (-orthonormalDiagonalOperator b a)) r := by
    intro r
    have hsub := (hU r).sub (hV r)
    convert hsub using 1
    noncomm_ring
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ t ht (A - B) (fun r => U r - V r) 0 hUV0
      (by intro r; simpa using hUV r)
  simpa [orthonormalDiagonalHamiltonian_rightSteadyState] using henv

/-- Left pairwise operator distance reaches every positive tolerance explicitly. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t → ‖U t - V t‖ ≤ ε := by
  intro t ht
  have hsettle := realFunction_abs_le_epsilon_after_exponentialBound
    δ ε ‖A - B‖ t₀ hδpos hε (norm_nonneg _) (fun s => ‖U s - V s‖)
    (by
      intro s hs
      have hc := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
        b a δ hδ hδpos t₀ s hs A B U V F hU0 hV0 hU hV
      simpa [abs_of_nonneg (norm_nonneg (U s - V s))] using hc)
    t ht
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hsettle

/-- Right pairwise operator distance has the identical waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t → ‖U t - V t‖ ≤ ε := by
  intro t ht
  have hsettle := realFunction_abs_le_epsilon_after_exponentialBound
    δ ε ‖A - B‖ t₀ hδpos hε (norm_nonneg _) (fun s => ‖U s - V s‖)
    (by
      intro s hs
      have hc := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
        b a δ hδ hδpos t₀ s hs A B U V F hU0 hV0 hU hV
      simpa [abs_of_nonneg (norm_nonneg (U s - V s))] using hc)
    t ht
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hsettle

/-- Left pairwise contraction acts pointwise. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r) :
    ‖(U t - V t) y‖ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖ := by
  have hc := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  exact (U t - V t).le_opNorm y |>.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg y))

/-- Right pairwise contraction acts pointwise. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖(U t - V t) y‖ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖ := by
  have hc := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  exact (U t - V t).le_opNorm y |>.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg y))

/-- Left pairwise matrix elements contract at the full gap. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
  have hp := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    b a δ hδ hδpos t₀ t ht A B U V F y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    _ ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ * ((‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg x)
    _ = _ := by ring

/-- Right pairwise matrix elements contract at the full gap. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
  have hp := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    b a δ hδ hδpos t₀ t ht A B U V F y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    _ ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ * ((‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg x)
    _ = _ := by ring

/-- Left pairwise matrix elements have an explicit vector-dependent waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
      |inner ℝ x ((U t - V t) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ hδpos hε (by positivity)
      (fun t => inner ℝ x ((U t - V t) y)) ?_
  intro t ht
  have hm := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    b a δ hδ hδpos t₀ t ht A B U V F x y hU0 hV0 hU hV
  calc
    _ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := hm
    _ = (‖A - B‖ * ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * δ)) := by ring

/-- Right pairwise matrix elements have the same explicit waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
      |inner ℝ x ((U t - V t) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ hδpos hε (by positivity)
      (fun t => inner ℝ x ((U t - V t) y)) ?_
  intro t ht
  have hm := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    b a δ hδ hδpos t₀ t ht A B U V F x y hU0 hV0 hU hV
  calc
    _ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := hm
    _ = (‖A - B‖ * ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * δ)) := by ring

/-- Left pairwise matrix elements settle uniformly on both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  exact (continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
    (U t) (V t) x y hx hy).trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ A B U V F hU0 hV0 hU hV ε hε t ht)

/-- Right pairwise matrix elements have the same unit-ball waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  exact (continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
    (U t) (V t) x y hx hy).trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ A B U V F hU0 hV0 hU hV ε hε t ht)

/-- Left common-input evolution is forward unique from equal initial data. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (hAB : A = B) : U t = V t := by
  have hc := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  have hz : ‖U t - V t‖ ≤ 0 := by simpa [hAB] using hc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- Right common-input evolution is forward unique from equal initial data. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i, δ ≤ a i) (hδpos : 0 < δ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r, HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hAB : A = B) : U t = V t := by
  have hc := orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  have hz : ‖U t - V t‖ ≤ 0 := by simpa [hAB] using hc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

end

end MathlibAnalytic
end MGAP4D
