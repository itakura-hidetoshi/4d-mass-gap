import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsPairVarianceBCF

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal

noncomputable section

private theorem continuous_compact_oriented_bcf_replaceLink_abs_le_norm
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    |O (C.base.replaceLink A target g)| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using
    O.norm_coe_le_norm (C.base.replaceLink A target g)

/-- Mean-square observable difference of two independent samples from the same
native one-link compact-Haar conditional law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalIndependentPairDifferenceEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) : ℝ :=
  ∫ z : C.base.Gauge × C.base.Gauge,
    (O (C.base.replaceLink A target z.1) -
      O (C.base.replaceLink A target z.2)) ^ 2
      ∂((C.singleLinkConditionalMeasure A target).prod
        (C.singleLinkConditionalMeasure A target))

/-- The one-link conditional independent-pair difference energy is nonnegative. -/
theorem continuous_compact_oriented_singleLinkConditionalIndependentPairDifferenceEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    0 ≤ C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalIndependentPairDifferenceEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The mean-square difference of two independent link samples from the exact
conditional Haar--Gibbs law is twice the native fiber conditional variance. -/
theorem continuous_compact_oriented_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_variance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A =
      2 * C.singleLinkConditionalVarianceBCF target O A := by
  let μ : Measure C.base.Gauge :=
    C.singleLinkConditionalMeasure A target
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
        C A target
  let f : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink A target g)
  have hfStrong : StronglyMeasurable f := by
    dsimp [f]
    exact
      (O.continuous.comp
        (continuous_compact_oriented_replaceLink C A target)).stronglyMeasurable
  have hfBound : ∀ g, |f g| ≤ ‖O‖ := by
    intro g
    exact continuous_compact_oriented_bcf_replaceLink_abs_le_norm
      O A target g
  let hConst : MemLp (fun _ : C.base.Gauge => ‖O‖) 2 μ :=
    memLp_const ‖O‖
  let hf : MemLp f 2 μ := by
    apply hConst.of_le hfStrong.aestronglyMeasurable
    filter_upwards [] with g
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg O)] using
      hfBound g
  let diff : C.base.Gauge × C.base.Gauge → ℝ :=
    fun z => f z.1 - f z.2
  have hDiff : MemLp diff 2 (μ.prod μ) := by
    dsimp [diff]
    exact (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hfInt : Integrable f μ := hf.integrable one_le_two
  have hMeanZero : ∫ z, diff z ∂(μ.prod μ) = 0 := by
    dsimp [diff]
    rw [integral_sub (hfInt.comp_fst μ) (hfInt.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  have hVarianceIntegral :
      ProbabilityTheory.variance diff (μ.prod μ) =
        ∫ z, (diff z) ^ 2 ∂(μ.prod μ) :=
    ProbabilityTheory.variance_of_integral_eq_zero
      hDiff.aemeasurable hMeanZero
  have hVarianceProd :=
    ProbabilityTheory.variance_add_prod (μ := μ) (ν := μ) hf hf.neg
  have hLocalVariance :
      ProbabilityTheory.variance f μ =
        C.singleLinkConditionalVarianceBCF target O A := by
    rw [ProbabilityTheory.variance_eq_integral hf.aemeasurable]
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalVarianceBCF
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
    rfl
  calc
    C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A =
        ProbabilityTheory.variance diff (μ.prod μ) := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalIndependentPairDifferenceEnergyBCF
      change (∫ z, (diff z) ^ 2 ∂(μ.prod μ)) = _
      exact hVarianceIntegral.symm
    _ = ProbabilityTheory.variance f μ +
        ProbabilityTheory.variance (fun g => -f g) μ := by
      simpa [diff, sub_eq_add_neg] using hVarianceProd
    _ = 2 * ProbabilityTheory.variance f μ := by
      rw [ProbabilityTheory.variance_fun_neg]
      ring
    _ = 2 * C.singleLinkConditionalVarianceBCF target O A := by
      rw [hLocalVariance]

/-- Gibbs averaging the independent conditional-pair difference energy gives
exactly twice the squared `L²` norm of the native one-link projection defect. -/
theorem continuous_compact_oriented_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure =
      2 * ‖C.singleLinkHeatBathFluctuationL2 target
        (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  calc
    (∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure) =
        ∫ A, 2 * C.singleLinkConditionalVarianceBCF target O A
          ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact
        continuous_compact_oriented_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_variance
          C target O A
    _ = 2 *
        ∫ A, C.singleLinkConditionalVarianceBCF target O A
          ∂C.gibbsMeasure := by
      rw [integral_const_mul]
    _ = 2 * ‖C.singleLinkHeatBathFluctuationL2 target
        (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
      rw [continuous_compact_oriented_integral_singleLinkConditionalVarianceBCF_eq_norm_sq]

/-- On the bounded-continuous core, the sum of all conditional independent-pair
difference energies is exactly twice the native heat-bath Hamiltonian quadratic
form. -/
theorem continuous_compact_oriented_sum_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_hamiltonian
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ target : C.base.geometry.Edge,
      ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure) =
      2 * inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) := by
  calc
    (∑ target : C.base.geometry.Edge,
      ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure) =
        ∑ target : C.base.geometry.Edge,
          2 * ‖C.singleLinkHeatBathFluctuationL2 target
            (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro target _
      exact
        continuous_compact_oriented_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_norm_sq
          C target O
    _ = 2 * ∑ target : C.base.geometry.Edge,
        ‖C.singleLinkHeatBathFluctuationL2 target
          (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = 2 * inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) := by
      rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]

end

end MathlibAnalytic
end MGAP4D
