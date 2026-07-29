import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelUniformForcingGain
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- Positive affine time rescaling tends to `+∞`.  This is the time-change used
when the exponentially damped transient is sent to zero. -/
theorem tendsto_sub_mul_atTop_atTop
    (t₀ δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => (t - t₀) * δ) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop (t₀ + b / δ)] with t ht
  have hdiv : b / δ ≤ t - t₀ := by
    linarith
  calc
    b = (b / δ) * δ := by
      rw [div_mul_cancel₀ b hδ.ne']
    _ ≤ (t - t₀) * δ :=
      mul_le_mul_of_nonneg_right hdiv hδ.le

/-- The shifted positive-rate exponential transient tends to zero at large real
time. -/
theorem tendsto_exp_neg_sub_mul_atTop_zero
    (t₀ δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => Real.exp (-((t - t₀) * δ))) atTop (nhds 0) := by
  simpa [Function.comp_def] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_sub_mul_atTop_atTop t₀ δ hδ)

/-- Any norm trajectory eventually dominated by a decaying exponential transient
plus a constant has limsup at most that constant. -/
theorem limsup_norm_le_of_eventually_le_exp_transient
    {X : Type*}
    [Norm X]
    (U : ℝ → X)
    (t₀ δ B c : ℝ)
    (hδ : 0 < δ)
    (hbound :
      ∀ᶠ t : ℝ in atTop,
        ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * B + c) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ c := by
  have hexp :
      Tendsto (fun t : ℝ => Real.exp (-((t - t₀) * δ))) atTop (nhds 0) :=
    tendsto_exp_neg_sub_mul_atTop_zero t₀ δ hδ
  have htransient :
      Tendsto
        (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * B)
        atTop (nhds 0) := by
    simpa only [zero_mul] using hexp.mul_const B
  have hconstant : Tendsto (fun _ : ℝ => c) atTop (nhds c) :=
    tendsto_const_nhds
  have henvelope :
      Tendsto
        (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * B + c)
        atTop (nhds c) := by
    simpa using htransient.add hconstant
  have hnormCobounded :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y)
        atTop (fun t : ℝ => ‖U t‖) :=
    Filter.isCoboundedUnder_le_of_le atTop
      (fun t : ℝ => norm_nonneg (U t))
  calc
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤
        Filter.limsup
          (fun t : ℝ => Real.exp (-((t - t₀) * δ)) * B + c) atTop :=
      Filter.limsup_le_limsup
        hbound hnormCobounded henvelope.isBoundedUnder_le
    _ = c := henvelope.limsup_eq

/-- Long-time input-to-state stability for the left operator-valued Hamiltonian
equation under a uniform forcing bound on the whole future half-line. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_left
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
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ M / δ := by
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg (F t₀)) (hFM t₀ le_rfl)
  have hbound :
      ∀ᶠ t : ℝ in atTop,
        ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ + M / δ := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
    exact
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
        b a δ hδ hδpos t₀ t ht A F U M hM hF
        (fun s hs => hFM s hs.1) hU0 hU
  exact
    limsup_norm_le_of_eventually_le_exp_transient
      U t₀ δ ‖A‖ (M / δ) hδpos hbound

/-- Long-time input-to-state stability for the right operator-valued Hamiltonian
equation, without a commutation hypothesis on the initial operator or forcing. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_right
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
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ M / δ := by
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg (F t₀)) (hFM t₀ le_rfl)
  have hbound :
      ∀ᶠ t : ℝ in atTop,
        ‖U t‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ + M / δ := by
    filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
    exact
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
        b a δ hδ hδpos t₀ t ht A F U M hM hF
        (fun s hs => hFM s hs.1) hU0 hU
  exact
    limsup_norm_le_of_eventually_le_exp_transient
      U t₀ δ ‖A‖ (M / δ) hδpos hbound

end

end MathlibAnalytic
end MGAP4D
