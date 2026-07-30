import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelMassGapBound
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcriticalScalar
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputUnitBallMatrixElementSteadyStateDifferenceFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- A uniformly bounded forcing mismatch contributes at most the input-to-state
    floor `C / δ` through the exponential memory kernel. -/
theorem intervalIntegral_exp_memory_mul_le_inputFloor
    (δ C t₀ t : ℝ) (ht : t₀ ≤ t) (hδpos : 0 < δ) (hC : 0 ≤ C)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hgC : ∀ s ∈ Set.Icc t₀ t, g s ≤ C) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤ C / δ := by
  have hleftContinuous : Continuous (fun s : ℝ =>
      Real.exp (-((t - s) * δ)) * g s) := by
    fun_prop
  have hrightContinuous : Continuous (fun s : ℝ =>
      Real.exp (-((t - s) * δ)) * C) := by
    fun_prop
  have hmono :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * C) := by
    apply intervalIntegral.integral_mono_on ht
      (hleftContinuous.intervalIntegrable t₀ t)
      (hrightContinuous.intervalIntegrable t₀ t)
    intro s hs
    exact mul_le_mul_of_nonneg_left (hgC s hs) (Real.exp_pos _).le
  have hfactor :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * C) =
        (∫ s in t₀..t, Real.exp (-((t - s) * δ))) * C := by
    rw [intervalIntegral.integral_mul_const]
  have hmemory :=
    intervalIntegral_exp_memory_to_end_le_inv δ t₀ t ht hδpos
  have hscaled :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ))) * C ≤ (1 / δ) * C :=
    mul_le_mul_of_nonneg_right hmemory hC
  calc
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * C := hmono
    _ = (∫ s in t₀..t, Real.exp (-((t - s) * δ))) * C := hfactor
    _ ≤ (1 / δ) * C := hscaled
    _ = C / δ := by ring

/-- Left Hamiltonian trajectories driven by inputs with uniformly bounded
    difference satisfy the canonical input-to-state estimate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ := by
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
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
      b a δ hδ t₀ t ht (A - B) (fun r : ℝ => F r - G r)
      (fun r : ℝ => U r - V r) hQ hW0 hW
  have hforcing :
      (∫ s in t₀..t,
        Real.exp (-((t - s) * δ)) * ‖F s - G s‖) ≤ C / δ :=
    intervalIntegral_exp_memory_mul_le_inputFloor
      δ C t₀ t ht hδpos hC (fun s : ℝ => ‖F s - G s‖) hQ.norm
      (by
        intro s hs
        exact hFG s hs.1)
  exact hmass.trans (add_le_add_left hforcing _)

/-- Right Hamiltonian trajectories satisfy the same input-to-state estimate
    without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ := by
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
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
      b a δ hδ t₀ t ht (A - B) (fun r : ℝ => F r - G r)
      (fun r : ℝ => U r - V r) hQ hW0 hW
  have hforcing :
      (∫ s in t₀..t,
        Real.exp (-((t - s) * δ)) * ‖F s - G s‖) ≤ C / δ :=
    intervalIntegral_exp_memory_mul_le_inputFloor
      δ C t₀ t ht hδpos hC (fun s : ℝ => ‖F s - G s‖) hQ.norm
      (by
        intro s hs
        exact hFG s hs.1)
  exact hmass.trans (add_le_add_left hforcing _)

/-- After the full-gap logarithmic waiting time, the left operator distance is
    within `ε` of the invariant input floor `C / δ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ‖U t - V t‖ ≤ C / δ + ε := by
  have htransient :=
    realFunction_abs_le_epsilon_after_exponentialBound
      δ ε ‖A - B‖ t₀ hδpos hε (norm_nonneg _)
      (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * ‖A - B‖)
      (by
        intro t ht
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
        simpa [mul_comm])
  intro t ht
  have ht₀ : t₀ ≤ t := by
    have hnonneg : 0 ≤ max 0 (Real.log (‖A - B‖ / ε) / δ) := le_max_left _ _
    linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
      b a δ hδ hδpos t₀ t ht₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV
  have hdecay : Real.exp (-((t - t₀) * δ)) * ‖A - B‖ ≤ ε := by
    simpa [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] using
      htransient t ht
  calc
    ‖U t - V t‖ ≤
        Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ := henv
    _ ≤ ε + C / δ := add_le_add_right hdecay _
    _ = C / δ + ε := by ring

/-- The right operator distance has the identical ultimate-bound waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ‖U t - V t‖ ≤ C / δ + ε := by
  have htransient :=
    realFunction_abs_le_epsilon_after_exponentialBound
      δ ε ‖A - B‖ t₀ hδpos hε (norm_nonneg _)
      (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * ‖A - B‖)
      (by
        intro t ht
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
        simpa [mul_comm])
  intro t ht
  have ht₀ : t₀ ≤ t := by
    have hnonneg : 0 ≤ max 0 (Real.log (‖A - B‖ / ε) / δ) := le_max_left _ _
    linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
      b a δ hδ hδpos t₀ t ht₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV
  have hdecay : Real.exp (-((t - t₀) * δ)) * ‖A - B‖ ≤ ε := by
    simpa [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] using
      htransient t ht
  calc
    ‖U t - V t‖ ≤
        Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ := henv
    _ ≤ ε + C / δ := add_le_add_right hdecay _
    _ = C / δ + ε := by ring

/-- The left input-to-state estimate acts pointwise on every vector. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
      b a δ hδ hδpos t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- The right input-to-state estimate has the same pointwise form. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
      b a δ hδ hδpos t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- Every left matrix element inherits the input-to-state envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_left
      b a δ hδ hδpos t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV
  have hcs :
      |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ *
        ((Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) *
          ‖x‖ * ‖y‖ := by ring

/-- Every right matrix element has the identical input-to-state envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_right
      b a δ hδ hδpos t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV
  have hcs :
      |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ *
        ((Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) *
          ‖x‖ * ‖y‖ := by ring

/-- Direct left matrix-element differences satisfy the same input-to-state envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_left
      b a δ hδ hδpos t₀ t ht A B F G U V C hC hF hG hFG
      x y hU0 hV0 hU hV

/-- Direct right matrix-element differences satisfy the identical envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_right
      b a δ hδ hδpos t₀ t ht A B F G U V C hC hF hG hFG
      x y hU0 hV0 hU hV

/-- A fixed left matrix element enters an `ε`-neighborhood of its input floor
    after the vector-dependent full-gap waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
          (C / δ) * ‖x‖ * ‖y‖ + ε := by
  have hcoeff : 0 ≤ ‖A - B‖ * ‖x‖ * ‖y‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg x)) (norm_nonneg y)
  have htransient :=
    realFunction_abs_le_epsilon_after_exponentialBound
      δ ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ hδpos hε hcoeff
      (fun t : ℝ =>
        Real.exp (-((t - t₀) * δ)) * ‖A - B‖ * ‖x‖ * ‖y‖)
      (by
        intro t ht
        rw [abs_of_nonneg
          (mul_nonneg
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
            (mul_nonneg (norm_nonneg x) (norm_nonneg y)))]
        ring)
  intro t ht
  have ht₀ : t₀ ≤ t := by
    have hnonneg : 0 ≤ max 0
        (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) := le_max_left _ _
    linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_left
      b a δ hδ hδpos t₀ t ht₀ A B F G U V C hC hF hG hFG
      x y hU0 hV0 hU hV
  have hdecay :
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ * ‖x‖ * ‖y‖ ≤ ε := by
    simpa [abs_of_nonneg
      (mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        (mul_nonneg (norm_nonneg x) (norm_nonneg y)))] using htransient t ht
  calc
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖x‖ * ‖y‖ := henv
    _ = Real.exp (-((t - t₀) * δ)) * ‖A - B‖ * ‖x‖ * ‖y‖ +
        (C / δ) * ‖x‖ * ‖y‖ := by ring
    _ ≤ ε + (C / δ) * ‖x‖ * ‖y‖ := add_le_add_right hdecay _
    _ = (C / δ) * ‖x‖ * ‖y‖ + ε := by ring

/-- The right fixed matrix element has the identical ultimate-bound waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : E) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
          (C / δ) * ‖x‖ * ‖y‖ + ε := by
  have hcoeff : 0 ≤ ‖A - B‖ * ‖x‖ * ‖y‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg x)) (norm_nonneg y)
  have htransient :=
    realFunction_abs_le_epsilon_after_exponentialBound
      δ ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ hδpos hε hcoeff
      (fun t : ℝ =>
        Real.exp (-((t - t₀) * δ)) * ‖A - B‖ * ‖x‖ * ‖y‖)
      (by
        intro t ht
        rw [abs_of_nonneg
          (mul_nonneg
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
            (mul_nonneg (norm_nonneg x) (norm_nonneg y)))]
        ring)
  intro t ht
  have ht₀ : t₀ ≤ t := by
    have hnonneg : 0 ≤ max 0
        (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / δ) := le_max_left _ _
    linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_right
      b a δ hδ hδpos t₀ t ht₀ A B F G U V C hC hF hG hFG
      x y hU0 hV0 hU hV
  have hdecay :
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ * ‖x‖ * ‖y‖ ≤ ε := by
    simpa [abs_of_nonneg
      (mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        (mul_nonneg (norm_nonneg x) (norm_nonneg y)))] using htransient t ht
  calc
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ + C / δ) * ‖x‖ * ‖y‖ := henv
    _ = Real.exp (-((t - t₀) * δ)) * ‖A - B‖ * ‖x‖ * ‖y‖ +
        (C / δ) * ‖x‖ * ‖y‖ := by ring
    _ ≤ ε + (C / δ) * ‖x‖ * ‖y‖ := add_le_add_right hdecay _
    _ = (C / δ) * ‖x‖ * ‖y‖ + ε := by ring

/-- A single full-gap waiting time controls every left matrix element on both
    closed unit balls up to the operator input floor. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ C / δ + ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_left
      b a δ hδ hδpos t₀ A B F G U V C hC hF hG hFG
      hU0 hV0 hU hV ε hε t ht)

/-- The right unit-ball result has the identical common waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / δ) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ C / δ + ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_right
      b a δ hδ hδpos t₀ A B F G U V C hC hF hG hFG
      hU0 hV0 hU hV ε hε t ht)

end

end MathlibAnalytic
end MGAP4D
