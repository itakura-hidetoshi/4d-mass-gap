import MGAP4D.MathlibAnalytic.FiniteZ2GaugeConfigurationUniformTransfer
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalCrossingUniformPoincare
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- A product of identical scalar factors separates from a finite list product. -/
theorem list_prod_map_const_mul
    {α : Type}
    (c : ℝ) (f : α → ℝ) (xs : List α) :
    (xs.map fun x => c * f x).prod =
      c ^ xs.length * (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, pow_succ]
      ring

/-- The actual local Wilson kernel is the positive local weight sum times the
normalized two-state kernel with sign-mode rate `q`. -/
theorem z2GaugeWilsonPlaquetteGramKernel_eq_weightSum_mul_normalized
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x y : Z2Gauge) :
    (z2GaugeWilsonPlaquetteGramKernel
        β energyIdentity energyNontrivial hβ hEnergy).kernel x y =
      z2WilsonTemporalCrossingWeightSum
          β energyIdentity energyNontrivial *
        finiteZ2NormalizedLocalKernel
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial)
          (boolEquivZ2Gauge.symm x)
          (boolEquivZ2Gauge.symm y) := by
  have hden :
      z2WilsonWeightIdentity β energyIdentity +
          z2WilsonWeightNontrivial β energyNontrivial ≠ 0 := by
    exact ne_of_gt <| add_pos
      (z2WilsonWeightIdentity_pos β energyIdentity)
      (z2WilsonWeightNontrivial_pos β energyNontrivial)
  have hdiag :
      z2WilsonWeightIdentity β energyIdentity =
        z2WilsonTemporalCrossingWeightSum
            β energyIdentity energyNontrivial *
          ((1 + z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) / 2) := by
    unfold z2WilsonTemporalCrossingRate
      z2WilsonTemporalCrossingWeightSum
    field_simp [hden]
    ring
  have hoff :
      z2WilsonWeightNontrivial β energyNontrivial =
        z2WilsonTemporalCrossingWeightSum
            β energyIdentity energyNontrivial *
          ((1 - z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) / 2) := by
    unfold z2WilsonTemporalCrossingRate
      z2WilsonTemporalCrossingWeightSum
    field_simp [hden]
    ring
  rw [z2GaugeWilsonPlaquetteGramKernel_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy]
    have hb : boolEquivZ2Gauge.symm x = boolEquivZ2Gauge.symm y :=
      congrArg boolEquivZ2Gauge.symm hxy
    simpa [finiteZ2NormalizedLocalKernel, hb] using hdiag
  · rw [if_neg hxy]
    have hb : boolEquivZ2Gauge.symm x ≠ boolEquivZ2Gauge.symm y := by
      intro h
      exact hxy ((boolEquivZ2Gauge.symm).injective h)
    simpa [finiteZ2NormalizedLocalKernel, hb] using hoff

/-- The temporal-link kernel has the same scalar-times-normalized local form. -/
theorem finiteEvenFourTorusZ2TemporalLinkGramKernel_eq_weightSum_mul_normalized
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (e : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalLinkGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy e).kernel A B =
      z2WilsonTemporalCrossingWeightSum
          β energyIdentity energyNontrivial *
        finiteZ2NormalizedLocalKernel
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial)
          (boolEquivZ2Gauge.symm (A e))
          (boolEquivZ2Gauge.symm (B e)) := by
  unfold finiteEvenFourTorusZ2TemporalLinkGramKernel
  rw [finiteOSGramKernelOn_comap_apply]
  exact z2GaugeWilsonPlaquetteGramKernel_eq_weightSum_mul_normalized
    β energyIdentity energyNontrivial hβ hEnergy (A e) (B e)

/-- Exact positive scalar relating the raw crossing kernel to its stochastic
normalization. -/
def finiteEvenFourTorusZ2TemporalCrossingScale
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  z2WilsonTemporalCrossingWeightSum
      β energyIdentity energyNontrivial ^
    Fintype.card (FiniteEvenFourTorusSpatialLink H)

/-- The crossing scale is strictly positive in every finite volume. -/
theorem finiteEvenFourTorusZ2TemporalCrossingScale_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) :
    0 < finiteEvenFourTorusZ2TemporalCrossingScale
      H β energyIdentity energyNontrivial := by
  exact pow_pos
    (z2WilsonTemporalCrossingWeightSum_pos
      β energyIdentity energyNontrivial) _

/-- The existing raw temporal crossing Gram kernel is exactly a positive scalar
multiple of the explicit normalized tensor kernel. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_scale_mul_normalized
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy).kernel A B =
      finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial *
        finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
          H β energyIdentity energyNontrivial A B := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
  rw [finite_os_gram_kernel_listProduct_apply]
  simp only [List.map_map, Function.comp_apply]
  simp_rw [finiteEvenFourTorusZ2TemporalLinkGramKernel_eq_weightSum_mul_normalized]
  rw [list_prod_map_const_mul]
  simp [finiteEvenFourTorusZ2TemporalCrossingScale,
    finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel,
    finiteZ2GaugeNormalizedProductKernel_apply]

/-- Finite kernel operators respect pointwise scalar multiplication. -/
theorem finiteKernelOperator_const_mul
    {α : Type} [Fintype α]
    (c : ℝ) (kernel : α → α → ℝ) :
    finiteKernelOperator (fun x y => c * kernel x y) =
      c • finiteKernelOperator kernel := by
  ext f y
  change (∑ x : α, (c * kernel x y) * f x) =
    c * ∑ x : α, kernel x y * f x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- Operator-level scalar identification of the existing raw crossing kernel. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_eq_scale_smul_normalized
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteKernelOperator
        (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel =
      finiteEvenFourTorusZ2TemporalCrossingScale
          H β energyIdentity energyNontrivial •
        finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
            H β energyIdentity energyNontrivial) := by
  rw [← finiteKernelOperator_const_mul
    (finiteEvenFourTorusZ2TemporalCrossingScale
      H β energyIdentity energyNontrivial)
    (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      H β energyIdentity energyNontrivial)]
  congr 1
  funext A B
  exact finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_scale_mul_normalized
    H β energyIdentity energyNontrivial hβ hEnergy A B

/-- The raw crossing operator norm is exactly the positive crossing scale. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_norm_eq_scale
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    ‖finiteKernelOperator
        (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel‖ =
      finiteEvenFourTorusZ2TemporalCrossingScale
        H β energyIdentity energyNontrivial := by
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_eq_scale_smul_normalized
    H β energyIdentity energyNontrivial hβ.le hEnergy.le]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (finiteEvenFourTorusZ2TemporalCrossingScale_pos
      H β energyIdentity energyNontrivial)]
  unfold finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
  rw [finiteZ2GaugeNormalizedProductKernel_operator_norm_eq_one
    (q := z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy).le
    (FiniteEvenFourTorusSpatialLink H)]
  ring

/-- Operator-norm normalization of the existing raw crossing kernel is exactly
the explicit dimension-free stochastic tensor transfer. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingNormalizedOperator_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel =
      finiteKernelOperator
        (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
          H β energyIdentity energyNontrivial) := by
  unfold finiteKernelNormalizedOperator
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_norm_eq_scale
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2TemporalGaugeCrossingOperator_eq_scale_smul_normalized
      H β energyIdentity energyNontrivial hβ.le hEnergy.le,
    smul_smul]
  rw [inv_mul_cancel₀
    (ne_of_gt (finiteEvenFourTorusZ2TemporalCrossingScale_pos
      H β energyIdentity energyNontrivial))]
  simp

/-- Explicit uniform temporal-crossing energy gap. -/
def z2WilsonTemporalCrossingGap
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  -Real.log
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)

/-- The explicit temporal-crossing gap is strictly positive. -/
theorem z2WilsonTemporalCrossingGap_pos
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 < z2WilsonTemporalCrossingGap
      β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingGap
  exact neg_pos.mpr
    (Real.log_neg
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy)
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))

/-- Exact exponential relation between the crossing gap and its contraction
rate. -/
theorem exp_neg_z2WilsonTemporalCrossingGap
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Real.exp (-z2WilsonTemporalCrossingGap
      β energyIdentity energyNontrivial) =
      z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial := by
  unfold z2WilsonTemporalCrossingGap
  rw [neg_neg, Real.exp_log
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy)]

/-- Uniform Poincare coercivity for the operator-norm normalized existing raw
crossing Gram kernel in every finite four-torus volume. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingNormalizedOperator_poincare
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (f : FiniteBoundaryHilbert
      (FiniteEvenFourTorusZ2SliceConfiguration H))
    (hmass : finiteFunctionMass f = 0) :
    z2WilsonTemporalCrossingCoercivity
          β energyIdentity energyNontrivial * ‖f‖ ^ 2 ≤
      inner ℝ
        (f - finiteKernelNormalizedOperator
          (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
            H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel f) f := by
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingNormalizedOperator_eq
    H β energyIdentity energyNontrivial hβ hEnergy]
  exact finiteEvenFourTorusZ2NormalizedTemporalCrossing_poincare
    H β energyIdentity energyNontrivial hβ hEnergy f hmass

end

end MathlibAnalytic
end MGAP4D
