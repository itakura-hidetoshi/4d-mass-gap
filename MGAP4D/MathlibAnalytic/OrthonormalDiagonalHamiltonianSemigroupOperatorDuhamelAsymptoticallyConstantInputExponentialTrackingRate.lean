import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputPracticalTrackingTime
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- The convolution of two distinct exponential rates has the standard
non-resonant difference-quotient form. -/
theorem intervalIntegral_exp_memory_mul_exp_tail_eq_div
    (δ μ t₀ t : ℝ)
    (hδμ : δ ≠ μ) :
    (∫ s in t₀..t,
      Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) =
      (Real.exp (-((t - t₀) * μ)) - Real.exp (-((t - t₀) * δ))) /
        (δ - μ) := by
  have hchange :=
    intervalIntegral.mul_integral_comp_mul_add
      (f := Real.exp) (a := t₀) (b := t) (δ - μ) (-δ * t + μ * t₀)
  rw [integral_exp] at hchange
  have hrewrite :
      (fun s : ℝ => Real.exp ((δ - μ) * s + (-δ * t + μ * t₀))) =
        fun s : ℝ =>
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrewrite] at hchange
  have hupper :
      (δ - μ) * t + (-δ * t + μ * t₀) = -((t - t₀) * μ) := by
    ring
  have hlower :
      (δ - μ) * t₀ + (-δ * t + μ * t₀) = -((t - t₀) * δ) := by
    ring
  have hmul :
      (δ - μ) *
          (∫ s in t₀..t,
            Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) =
        Real.exp (-((t - t₀) * μ)) - Real.exp (-((t - t₀) * δ)) := by
    simpa [hupper, hlower] using hchange
  apply (eq_div_iff (sub_ne_zero.mpr hδμ)).2
  simpa [mul_comm] using hmul

/-- At resonance, the exponential convolution acquires the linear prefactor
`t - t₀`. -/
theorem intervalIntegral_exp_memory_mul_exp_tail_eq_resonant
    (δ t₀ t : ℝ) :
    (∫ s in t₀..t,
      Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * δ))) =
      (t - t₀) * Real.exp (-((t - t₀) * δ)) := by
  have hrewrite :
      (fun s : ℝ =>
        Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * δ))) =
        fun _ : ℝ => Real.exp (-((t - t₀) * δ)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrewrite]
  simp [smul_eq_mul]

/-- A pointwise non-resonant exponential tail controls the weighted memory
integral by the exact difference quotient. -/
theorem intervalIntegral_exp_memory_mul_le_exponential_tail_nonresonant
    (δ μ C t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (hδμ : δ ≠ μ)
    (g : ℝ → ℝ)
    (hg : Continuous g)
    (hgC : ∀ s ∈ Set.Icc t₀ t,
      g s ≤ C * Real.exp (-((s - t₀) * μ))) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
      ((Real.exp (-((t - t₀) * μ)) - Real.exp (-((t - t₀) * δ))) /
        (δ - μ)) * C := by
  have hleftContinuous :
      Continuous (fun s : ℝ => Real.exp (-((t - s) * δ)) * g s) := by
    fun_prop
  have hleftIntegrable :
      IntervalIntegrable
        (fun s : ℝ => Real.exp (-((t - s) * δ)) * g s)
        volume t₀ t :=
    hleftContinuous.intervalIntegrable t₀ t
  have hrightContinuous :
      Continuous (fun s : ℝ =>
        Real.exp (-((t - s) * δ)) *
          (C * Real.exp (-((s - t₀) * μ)))) := by
    fun_prop
  have hrightIntegrable :
      IntervalIntegrable
        (fun s : ℝ =>
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * μ))))
        volume t₀ t :=
    hrightContinuous.intervalIntegrable t₀ t
  have hmono :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * μ))) := by
    apply intervalIntegral.integral_mono_on ht hleftIntegrable hrightIntegrable
    intro s hs
    exact mul_le_mul_of_nonneg_left (hgC s hs) (Real.exp_pos _).le
  calc
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * μ))) := hmono
    _ = (∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) * C := by
      have hfun :
          (fun s : ℝ =>
            Real.exp (-((t - s) * δ)) *
              (C * Real.exp (-((s - t₀) * μ)))) =
            fun s : ℝ =>
              (Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * μ))) * C := by
        funext s
        ring
      rw [hfun, intervalIntegral.integral_mul_const]
    _ = ((Real.exp (-((t - t₀) * μ)) - Real.exp (-((t - t₀) * δ))) /
          (δ - μ)) * C := by
      rw [intervalIntegral_exp_memory_mul_exp_tail_eq_div δ μ t₀ t hδμ]

/-- A resonant exponential tail controls the weighted memory integral by the
linear-exponential response. -/
theorem intervalIntegral_exp_memory_mul_le_exponential_tail_resonant
    (δ C t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (g : ℝ → ℝ)
    (hg : Continuous g)
    (hgC : ∀ s ∈ Set.Icc t₀ t,
      g s ≤ C * Real.exp (-((s - t₀) * δ))) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := by
  have hleftContinuous :
      Continuous (fun s : ℝ => Real.exp (-((t - s) * δ)) * g s) := by
    fun_prop
  have hleftIntegrable :
      IntervalIntegrable
        (fun s : ℝ => Real.exp (-((t - s) * δ)) * g s)
        volume t₀ t :=
    hleftContinuous.intervalIntegrable t₀ t
  have hrightContinuous :
      Continuous (fun s : ℝ =>
        Real.exp (-((t - s) * δ)) *
          (C * Real.exp (-((s - t₀) * δ)))) := by
    fun_prop
  have hrightIntegrable :
      IntervalIntegrable
        (fun s : ℝ =>
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * δ))))
        volume t₀ t :=
    hrightContinuous.intervalIntegrable t₀ t
  have hmono :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * δ))) := by
    apply intervalIntegral.integral_mono_on ht hleftIntegrable hrightIntegrable
    intro s hs
    exact mul_le_mul_of_nonneg_left (hgC s hs) (Real.exp_pos _).le
  calc
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) *
            (C * Real.exp (-((s - t₀) * δ))) := hmono
    _ = (∫ s in t₀..t,
          Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * δ))) * C := by
      have hfun :
          (fun s : ℝ =>
            Real.exp (-((t - s) * δ)) *
              (C * Real.exp (-((s - t₀) * δ)))) =
            fun s : ℝ =>
              (Real.exp (-((t - s) * δ)) * Real.exp (-((s - t₀) * δ))) * C := by
        funext s
        ring
      rw [hfun, intervalIntegral.integral_mul_const]
    _ = ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := by
      rw [intervalIntegral_exp_memory_mul_exp_tail_eq_resonant δ t₀ t]

/-- Non-resonant closed-form tracking rate for left Hamiltonian multiplication. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_left
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
    (hδμ : δ ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
        ((Real.exp (-((t - t₀) * μ)) - Real.exp (-((t - t₀) * δ))) /
          (δ - μ)) * C := by
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
    intervalIntegral_exp_memory_mul_le_exponential_tail_nonresonant
      δ μ C t₀ t ht hδμ (fun s : ℝ => ‖G s‖) hG.norm
      (by
        intro s hs
        simpa [G] using hFC s hs)
  simpa [V, S] using hmass.trans (add_le_add (le_refl _) hforcing)

/-- Non-resonant closed-form tracking rate for right Hamiltonian multiplication. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_right
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
    (hδμ : δ ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
        ((Real.exp (-((t - t₀) * μ)) - Real.exp (-((t - t₀) * δ))) /
          (δ - μ)) * C := by
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
    intervalIntegral_exp_memory_mul_le_exponential_tail_nonresonant
      δ μ C t₀ t ht hδμ (fun s : ℝ => ‖G s‖) hG.norm
      (by
        intro s hs
        simpa [G] using hFC s hs)
  simpa [V, S] using hmass.trans (add_le_add (le_refl _) hforcing)

/-- Resonant closed-form tracking rate for left Hamiltonian multiplication. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
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
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
        ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := by
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
    intervalIntegral_exp_memory_mul_le_exponential_tail_resonant
      δ C t₀ t ht (fun s : ℝ => ‖G s‖) hG.norm
      (by
        intro s hs
        simpa [G] using hFC s hs)
  simpa [V, S] using hmass.trans (add_le_add (le_refl _) hforcing)

/-- Resonant closed-form tracking rate for right Hamiltonian multiplication. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
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
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
        ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := by
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
    intervalIntegral_exp_memory_mul_le_exponential_tail_resonant
      δ C t₀ t ht (fun s : ℝ => ‖G s‖) hG.norm
      (by
        intro s hs
        simpa [G] using hFC s hs)
  simpa [V, S] using hmass.trans (add_le_add (le_refl _) hforcing)

end

end MathlibAnalytic
end MGAP4D
