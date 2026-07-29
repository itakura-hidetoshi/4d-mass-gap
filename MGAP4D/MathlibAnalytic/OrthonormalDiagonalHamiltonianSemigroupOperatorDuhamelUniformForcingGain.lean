import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelMassGapBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- The forward exponential memory kernel has total mass
`(1 - exp (-(t - t₀)δ)) / δ` when `δ ≠ 0`.

This is the scalar identity that converts the Duhamel convolution estimate into
an explicit input-to-state gain. -/
theorem intervalIntegral_exp_neg_sub_mul_eq_one_sub_exp_div
    (δ t₀ t : ℝ)
    (hδ : δ ≠ 0) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ))) =
      (1 - Real.exp (-((t - t₀) * δ))) / δ := by
  have hchange :=
    intervalIntegral.mul_integral_comp_mul_add
      (f := Real.exp) (a := t₀) (b := t) δ (-δ * t)
  rw [integral_exp] at hchange
  have hrewrite :
      (fun s : ℝ => Real.exp (δ * s + -δ * t)) =
        fun s : ℝ => Real.exp (-((t - s) * δ)) := by
    funext s
    congr 1
    ring
  rw [hrewrite] at hchange
  have hupper : δ * t + -(δ * t) = 0 := by ring
  have hlower : δ * t₀ + -(δ * t) = -((t - t₀) * δ) := by ring
  have hmul :
      δ * (∫ s in t₀..t, Real.exp (-((t - s) * δ))) =
        1 - Real.exp (-((t - t₀) * δ)) := by
    simpa [hupper, hlower] using hchange
  apply (eq_div_iff hδ).2
  simpa [mul_comm] using hmul

/-- A pointwise uniform bound on an input controls its exponentially weighted
Duhamel integral by the exact finite-time gain. -/
theorem intervalIntegral_exp_neg_sub_mul_le_uniform_gain
    (δ M t₀ t : ℝ)
    (hδ : 0 < δ)
    (ht : t₀ ≤ t)
    (g : ℝ → ℝ)
    (hg : Continuous g)
    (hgM : ∀ s ∈ Set.Icc t₀ t, g s ≤ M) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M := by
  have hleftContinuous :
      Continuous (fun s : ℝ => Real.exp (-((t - s) * δ)) * g s) := by
    fun_prop
  have hleftIntegrable :
      IntervalIntegrable
        (fun s : ℝ => Real.exp (-((t - s) * δ)) * g s)
        volume t₀ t :=
    hleftContinuous.intervalIntegrable t₀ t
  have hrightContinuous :
      Continuous (fun s : ℝ => Real.exp (-((t - s) * δ)) * M) := by
    fun_prop
  have hrightIntegrable :
      IntervalIntegrable
        (fun s : ℝ => Real.exp (-((t - s) * δ)) * M)
        volume t₀ t :=
    hrightContinuous.intervalIntegrable t₀ t
  have hmono :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * M := by
    apply intervalIntegral.integral_mono_on ht hleftIntegrable hrightIntegrable
    intro s hs
    exact mul_le_mul_of_nonneg_left (hgM s hs) (Real.exp_pos _).le
  calc
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * g s) ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * M := hmono
    _ = (∫ s in t₀..t, Real.exp (-((t - s) * δ))) * M := by
      rw [intervalIntegral.integral_mul_const]
    _ = ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M := by
      rw [intervalIntegral_exp_neg_sub_mul_eq_one_sub_exp_div δ t₀ t hδ.ne']

/-- The finite-time exponential gain is bounded by the static gain `1 / δ`. -/
theorem one_sub_exp_neg_mul_div_le_inv
    (δ τ : ℝ)
    (hδ : 0 < δ)
    (hτ : 0 ≤ τ) :
    (1 - Real.exp (-(τ * δ))) / δ ≤ 1 / δ := by
  apply (div_le_div_iff_of_pos_right hδ).2
  have hexp : 0 ≤ Real.exp (-(τ * δ)) := (Real.exp_pos _).le
  have hexp_le_one : Real.exp (-(τ * δ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hτ hδ.le))
  linarith

/-- Input-to-state gain for the left operator-valued Hamiltonian equation under
a uniformly bounded forcing term. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
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
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M := by
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
      b a δ hδ t₀ t ht A F U hF hU0 hU
  have hforcing :=
    intervalIntegral_exp_neg_sub_mul_le_uniform_gain
      δ M t₀ t hδpos ht (fun s : ℝ => ‖F s‖) hF.norm hFM
  exact hmass.trans (add_le_add_left hforcing _)

/-- Input-to-state gain for the right operator-valued Hamiltonian equation under
a uniformly bounded forcing term, with no Hamiltonian-commutation assumption. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
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
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M := by
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
      b a δ hδ t₀ t ht A F U hF hU0 hU
  have hforcing :=
    intervalIntegral_exp_neg_sub_mul_le_uniform_gain
      δ M t₀ t hδpos ht (fun s : ℝ => ‖F s‖) hF.norm hFM
  exact hmass.trans (add_le_add_left hforcing _)

/-- The left equation is bounded by an exponentially decaying transient plus the
static input gain `M / δ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
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
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ + M / δ := by
  have hgain :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
      b a δ hδ hδpos t₀ t ht A F U M hF hFM hU0 hU
  have hratio :=
    one_sub_exp_neg_mul_div_le_inv δ (t - t₀) hδpos (sub_nonneg.mpr ht)
  have hweighted :
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ M / δ := by
    calc
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ (1 / δ) * M :=
        mul_le_mul_of_nonneg_right hratio hM
      _ = M / δ := by ring
  exact hgain.trans (add_le_add_left hweighted _)

/-- The right equation has the same static input gain `M / δ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
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
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ + M / δ := by
  have hgain :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
      b a δ hδ hδpos t₀ t ht A F U M hF hFM hU0 hU
  have hratio :=
    one_sub_exp_neg_mul_div_le_inv δ (t - t₀) hδpos (sub_nonneg.mpr ht)
  have hweighted :
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ M / δ := by
    calc
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * M ≤ (1 / δ) * M :=
        mul_le_mul_of_nonneg_right hratio hM
      _ = M / δ := by ring
  exact hgain.trans (add_le_add_left hweighted _)

end

end MathlibAnalytic
end MGAP4D
