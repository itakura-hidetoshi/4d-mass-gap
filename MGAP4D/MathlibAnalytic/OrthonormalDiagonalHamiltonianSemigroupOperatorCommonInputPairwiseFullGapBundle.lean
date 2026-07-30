import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputUnitBallMatrixElementSteadyStateDifferenceFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two left Hamiltonian trajectories driven by the same arbitrary time-dependent
    input contract at the full spectral-gap rate. The common input cancels in the
    difference equation, so no regularity or decay assumption on the input is needed. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r) :
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

/-- Two right Hamiltonian trajectories driven by the same arbitrary time-dependent
    input have the identical full-gap contraction estimate, without a commutation
    hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r) :
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

/-- Left pairwise operator distance reaches every positive tolerance after the
    full-gap logarithmic waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε ‖A - B‖ t₀ hδpos hε (norm_nonneg _) (fun t : ℝ => ‖U t - V t‖) ?_
  intro t ht
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hcontract

/-- Right pairwise operator distance has the identical explicit waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε ‖A - B‖ t₀ hδpos hε (norm_nonneg _) (fun t : ℝ => ‖U t - V t‖) ?_
  intro t ht
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hcontract

/-- Left pairwise contraction acts pointwise on every vector. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖ := by
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)

/-- Right pairwise contraction has the identical pointwise estimate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖ := by
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)

/-- Every left matrix element of the pairwise error contracts at the full gap. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ t ht A B U V F y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ * ((‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by ring

/-- Every right matrix element has the identical pairwise full-gap estimate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ t ht A B U V F y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ * ((‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by ring

/-- A left pairwise matrix element reaches every tolerance after the corresponding
    vector-dependent logarithmic waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x ((U t - V t) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ hδpos hε (by positivity)
      (fun t : ℝ => inner ℝ x ((U t - V t) y)) ?_
  intro t ht
  have hmatrix :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ t ht A B U V F x y hU0 hV0 hU hV
  calc
    |inner ℝ x ((U t - V t) y)| ≤
        (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := hmatrix
    _ = (‖A - B‖ * ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * δ)) := by ring

/-- A right pairwise matrix element has the identical explicit waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E)) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x ((U t - V t) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ hδpos hε (by positivity)
      (fun t : ℝ => inner ℝ x ((U t - V t) y)) ?_
  intro t ht
  have hmatrix :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ t ht A B U V F x y hU0 hV0 hU hV
  calc
    |inner ℝ x ((U t - V t) y)| ≤
        (‖A - B‖ * Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := hmatrix
    _ = (‖A - B‖ * ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * δ)) := by ring

/-- After the operator-norm waiting time, all left pairwise matrix elements on the
    two closed unit balls are simultaneously within the tolerance. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ A B U V F hU0 hV0 hU hV ε hε t ht)

/-- The right pairwise unit-ball estimate has the identical waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ A B U V F hU0 hV0 hU hV ε hε t ht)

/-- Left evolution under an arbitrary common input is forward unique from equal
    initial operators. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F r) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Right evolution under an arbitrary common input is forward unique from equal
    initial operators, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F : ℝ → (E →L[ℝ] E))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ t ht A B U V F hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end

end MathlibAnalytic
end MGAP4D
