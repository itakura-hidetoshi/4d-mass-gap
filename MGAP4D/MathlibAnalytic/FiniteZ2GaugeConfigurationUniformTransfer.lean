import MGAP4D.MathlibAnalytic.FiniteZ2GaugeConfigurationUniformPoincare
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Pointwise product formula for the normalized kernel on an arbitrary finite
actual `Z₂` configuration carrier. -/
theorem finiteZ2GaugeNormalizedProductKernel_apply
    (q : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (A B : ι → Z2Gauge) :
    finiteZ2GaugeNormalizedProductKernel q ι A B =
      ∏ e : ι,
        finiteZ2NormalizedLocalKernel q
          (boolEquivZ2Gauge.symm (A e))
          (boolEquivZ2Gauge.symm (B e)) := by
  unfold finiteZ2GaugeNormalizedProductKernel
  rw [finiteZ2NormalizedProductKernel_apply]
  refine Fintype.prod_equiv (Fintype.equivFin ι).symm _ _ ?_
  intro i
  simp [finiteZ2GaugeConfigurationEquiv]

/-- Full quadratic-form positivity and contraction of the transported product
kernel, not merely on the centered sector. -/
theorem finiteZ2GaugeNormalizedProductKernel_quadratic_mem_normInterval
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : (ι → Z2Gauge) → ℝ) :
    0 ≤ finiteFunctionKernelQuadratic
        (finiteZ2GaugeNormalizedProductKernel q ι) f ∧
      finiteFunctionKernelQuadratic
          (finiteZ2GaugeNormalizedProductKernel q ι) f ≤
        finiteFunctionNormSq f := by
  let g : (Fin (Fintype.card ι) → Bool) → ℝ :=
    fun b => f ((finiteZ2GaugeConfigurationEquiv ι).symm b)
  have hbound :=
    finiteZ2NormalizedProductKernel_quadratic_mem_normInterval
      hq0 hq1 (Fintype.card ι) g
  rw [finiteZ2GaugeNormalizedProductKernel_quadratic_equiv]
  rw [finiteZ2GaugeConfiguration_normSq_equiv ι f]
  simpa [g] using hbound

/-- Every column of the actual-carrier normalized product kernel has mass one. -/
theorem finiteZ2GaugeNormalizedProductKernel_row_sum
    (q : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Z2Gauge) :
    ∑ A : ι → Z2Gauge,
      finiteZ2GaugeNormalizedProductKernel q ι A B = 1 := by
  let e := finiteZ2GaugeConfigurationEquiv ι
  calc
    (∑ A : ι → Z2Gauge,
        finiteZ2GaugeNormalizedProductKernel q ι A B) =
      ∑ b : Fin (Fintype.card ι) → Bool,
        finiteZ2GaugeNormalizedProductKernel q ι (e.symm b) B := by
      refine Fintype.sum_equiv e _ _ ?_
      intro A
      simp
    _ = ∑ b : Fin (Fintype.card ι) → Bool,
        finiteZ2NormalizedProductKernel q (Fintype.card ι) b (e B) := by
      apply Finset.sum_congr rfl
      intro b _hb
      simp [e, finiteZ2GaugeNormalizedProductKernel]
    _ = 1 :=
      finiteZ2NormalizedProductKernel_row_sum q (Fintype.card ι) (e B)

/-- The transported product transfer fixes the actual-carrier constant mode. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_constantOne
    (q : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    finiteKernelOperator (finiteZ2GaugeNormalizedProductKernel q ι)
        finiteBoundaryConstantOne =
      finiteBoundaryConstantOne := by
  ext B
  rw [finiteKernelOperator_apply]
  simp only [finiteBoundaryConstantOne_apply, mul_one]
  exact finiteZ2GaugeNormalizedProductKernel_row_sum q ι B

/-- The transported product transfer has operator norm at most one. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_norm_le_one
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    ‖finiteKernelOperator (finiteZ2GaugeNormalizedProductKernel q ι)‖ ≤ 1 := by
  let T := finiteKernelOperator (finiteZ2GaugeNormalizedProductKernel q ι)
  have hsymm : T.toLinearMap.IsSymmetric :=
    finiteKernelOperator_isSymmetric _
      (finiteZ2GaugeNormalizedProductKernel_symmetric q ι)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsymm]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · have hinterval :=
      finiteZ2GaugeNormalizedProductKernel_quadratic_mem_normInterval
        hq0 hq1 ι f
    have hquadratic :
        finiteFunctionKernelQuadratic
            (finiteZ2GaugeNormalizedProductKernel q ι) f =
          inner ℝ (T f) f :=
      finiteFunctionKernelQuadratic_eq_inner_operator _ f
    have hnorm : finiteFunctionNormSq f = ‖f‖ ^ 2 :=
      finiteFunctionNormSq_eq_norm_sq f
    have hden : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
    have hnonneg : 0 ≤ T.rayleighQuotient f := by
      change 0 ≤ inner ℝ (T f) f / ‖f‖ ^ 2
      apply div_nonneg
      · simpa [← hquadratic] using hinterval.1
      · exact hden.le
    have hle : T.rayleighQuotient f ≤ 1 := by
      change inner ℝ (T f) f / ‖f‖ ^ 2 ≤ 1
      rw [div_le_one hden]
      simpa [← hquadratic, ← hnorm] using hinterval.2
    simpa [abs_of_nonneg hnonneg] using hle

/-- The transported product transfer has operator norm at least one. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_one_le_norm
    (q : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    1 ≤ ‖finiteKernelOperator (finiteZ2GaugeNormalizedProductKernel q ι)‖ := by
  let T := finiteKernelOperator (finiteZ2GaugeNormalizedProductKernel q ι)
  let one : FiniteBoundaryHilbert (ι → Z2Gauge) := finiteBoundaryConstantOne
  have hone : one ≠ 0 := by
    intro hzero
    have hvalue := congrArg
      (fun f : FiniteBoundaryHilbert (ι → Z2Gauge) => f default) hzero
    simp [one, finiteBoundaryConstantOne] at hvalue
  have hfix : T one = one :=
    finiteZ2GaugeNormalizedProductKernel_operator_constantOne q ι
  have hbound := T.le_opNorm one
  rw [hfix] at hbound
  have honeNorm : 0 < ‖one‖ := norm_pos_iff.mpr hone
  nlinarith [norm_nonneg T]

/-- The transported stochastic symmetric positive transfer has exact operator
norm one. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_norm_eq_one
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    ‖finiteKernelOperator (finiteZ2GaugeNormalizedProductKernel q ι)‖ = 1 :=
  le_antisymm
    (finiteZ2GaugeNormalizedProductKernel_operator_norm_le_one hq0 hq1 ι)
    (finiteZ2GaugeNormalizedProductKernel_operator_one_le_norm q ι)

end

end MathlibAnalytic
end MGAP4D
