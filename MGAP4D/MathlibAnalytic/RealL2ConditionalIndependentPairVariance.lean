import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Exact independent-pair normalization on an existing conditional L2 carrier

Two independent samples of the SAME probability law have mean-square
observable difference equal to twice the variance. This is an equality, not a
triangle-inequality loss. The conditional version evaluates an existing L2
vector by its a.e. representative; it does not introduce a new carrier or
identify different measure-indexed L2 types.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The exact two-sample normalization, with finite second moment. -/
theorem realProbabilityIndependentPair_lintegral_sq_sub_eq_two_mul_evariance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) :
    (∫⁻ uv : α × α, ENNReal.ofReal ((X uv.1 - X uv.2) ^ 2) ∂μ.prod μ) =
      2 * evariance X μ := by
  let D : α × α → ℝ := fun z => X z.1 - X z.2
  have hD : MemLp D 2 (μ.prod μ) :=
    (hX.comp_fst μ).sub (hX.comp_snd μ)
  have hXInt : Integrable X μ := hX.integrable one_le_two
  have hMean : (∫ z, D z ∂μ.prod μ) = 0 := by
    dsimp [D]
    rw [integral_sub (hXInt.comp_fst μ) (hXInt.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  have hVar : variance D (μ.prod μ) = 2 * variance X μ := by
    calc
      variance D (μ.prod μ) = variance X μ + variance (fun a => -X a) μ := by
        simpa only [D, sub_eq_add_neg] using
          (variance_add_prod (μ := μ) (ν := μ) hX hX.neg)
      _ = 2 * variance X μ := by
        rw [variance_fun_neg]
        ring
  calc
    (∫⁻ uv : α × α, ENNReal.ofReal ((X uv.1 - X uv.2) ^ 2) ∂μ.prod μ) =
        evariance D (μ.prod μ) := by
      rw [evariance_eq_lintegral_ofReal, hMean]
      simp only [sub_zero, D]
    _ = ENNReal.ofReal (variance D (μ.prod μ)) := hD.ofReal_variance_eq.symm
    _ = ENNReal.ofReal (2 * variance X μ) := by rw [hVar]
    _ = 2 * evariance X μ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hX.ofReal_variance_eq]
      norm_num

/-- An existing conditional independent-pair L2 vector whose representative
is the difference of two evaluations of one section has norm square equal to
twice the integrated fiber variance. No ambient representative is evaluated
pointwise without the explicit a.e. receipt. -/
theorem realL2_conditionalIndependentPair_norm_sq_eq_two_mul_lintegral_evariance
    {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α γ) [IsMarkovKernel κ]
    (M : α × γ → ℝ) (hM : StronglyMeasurable M)
    (hFiber : ∀ a, MemLp (fun u => M (a, u)) 2 (κ a))
    (L : Lp ℝ 2 (μ ⊗ₘ (κ ×ₖ κ)))
    (hRep : (fun z => L z) =ᵐ[μ ⊗ₘ (κ ×ₖ κ)]
      (fun z => M (z.1, z.2.1) - M (z.1, z.2.2))) :
    ENNReal.ofReal (‖L‖ ^ 2) =
      2 * ∫⁻ a, evariance (fun u => M (a, u)) (κ a) ∂μ := by
  let D : α × (γ × γ) → ℝ :=
    fun z => M (z.1, z.2.1) - M (z.1, z.2.2)
  have hDStrong : StronglyMeasurable D :=
    (hM.comp_measurable
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).sub
      (hM.comp_measurable
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hD : MemLp D 2 (μ ⊗ₘ (κ ×ₖ κ)) := (memLp_congr_ae hRep).mp (_root_.MeasureTheory.Lp.memLp L)
  have hNorm : ‖L‖ ^ 2 = ∫ z, (D z) ^ 2 ∂(μ ⊗ₘ (κ ×ₖ κ)) := by
    rw [realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hRep] with z hz
    rw [hz]
    simp only [D, Real.norm_eq_abs, sq_abs]
  have hSqInt : Integrable (fun z => (D z) ^ 2) (μ ⊗ₘ (κ ×ₖ κ)) := by
    simpa only [Pi.pow_apply] using hD.integrable_sq
  have hPhi : Measurable (fun z => ENNReal.ofReal ((D z) ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp (hDStrong.measurable.pow_const 2)
  calc
    ENNReal.ofReal (‖L‖ ^ 2) =
        ∫⁻ z, ENNReal.ofReal ((D z) ^ 2) ∂(μ ⊗ₘ (κ ×ₖ κ)) := by
      rw [hNorm]
      exact ofReal_integral_eq_lintegral_ofReal hSqInt
        (ae_of_all _ fun z => sq_nonneg (D z))
    _ = ∫⁻ a, ∫⁻ uv, ENNReal.ofReal ((D (a, uv)) ^ 2) ∂(κ ×ₖ κ) a ∂μ :=
      Measure.lintegral_compProd hPhi
    _ = ∫⁻ a, 2 * evariance (fun u => M (a, u)) (κ a) ∂μ := by
      apply lintegral_congr
      intro a
      rw [Kernel.prod_apply]
      exact realProbabilityIndependentPair_lintegral_sq_sub_eq_two_mul_evariance
        (κ a) (fun u => M (a, u)) (hFiber a)
    _ = 2 * ∫⁻ a, evariance (fun u => M (a, u)) (κ a) ∂μ :=
      lintegral_const_mul' 2 _ (by simp)

end

end MGAP4D.MathlibAnalytic
