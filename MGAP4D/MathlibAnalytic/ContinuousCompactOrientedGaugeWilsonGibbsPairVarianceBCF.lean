import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalVarianceBCF
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathPoincareL2
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable section

private theorem continuous_compact_oriented_bcf_abs_le_norm_pair
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- Every bounded continuous observable belongs to the native Gibbs `L²` space. -/
theorem continuous_compact_oriented_bcf_memLp_two
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    MemLp O 2 C.gibbsMeasure :=
  continuous_compact_oriented_memLp_two_of_uniform_bound
    C O O.continuous.stronglyMeasurable ‖O‖ (norm_nonneg _)
    (continuous_compact_oriented_bcf_abs_le_norm_pair O)

/-- Gibbs variance of a bounded continuous observable on the genuine compact
configuration space. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsVarianceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ProbabilityTheory.variance O C.gibbsMeasure

/-- Mean-square difference of two independent Gibbs configurations.  This is
the coupling-ready representation of global variance. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsIndependentPairDifferenceEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z : C.base.Configuration × C.base.Configuration,
    (O z.1 - O z.2) ^ 2 ∂(C.gibbsMeasure.prod C.gibbsMeasure)

/-- Independent-pair difference energy is nonnegative. -/
theorem continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.gibbsIndependentPairDifferenceEnergyBCF O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsIndependentPairDifferenceEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The squared norm of the canonical Gibbs `L²` representative is its Gibbs
second moment. -/
theorem continuous_compact_oriented_gibbsL2RepresentativeBCF_norm_sq_eq_integral_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    ‖C.gibbsL2RepresentativeBCF O‖ ^ 2 =
      ∫ A, (O A) ^ 2 ∂C.gibbsMeasure := by
  let hO : MemLp O 2 C.gibbsMeasure :=
    continuous_compact_oriented_bcf_memLp_two C O
  have hRep : C.gibbsL2RepresentativeBCF O = hO.toLp O := by
    rfl
  rw [hRep, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hO.coeFn_toLp] with A hA
  rw [hA]
  simp [pow_two]

/-- Pairing the canonical Gibbs representative with the normalized Gibbs vacuum
is exactly Gibbs expectation. -/
theorem continuous_compact_oriented_inner_gibbsVacuumL2_gibbsL2RepresentativeBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    inner ℝ C.gibbsVacuumL2 (C.gibbsL2RepresentativeBCF O) =
      ∫ A, O A ∂C.gibbsMeasure := by
  let hO : MemLp O 2 C.gibbsMeasure :=
    continuous_compact_oriented_bcf_memLp_two C O
  have hRep : C.gibbsL2RepresentativeBCF O = hO.toLp O := by
    rfl
  have hVacuum :
      (C.gibbsVacuumL2 : C.base.Configuration → ℝ) =ᵐ[C.gibbsMeasure]
        fun _ => (1 : ℝ) := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumL2
    simpa using
      (indicatorConstLp_coeFn
        (μ := C.gibbsMeasure)
        (p := (2 : ℝ≥0∞))
        (s := Set.univ)
        (hs := MeasurableSet.univ)
        (hμs := by finiteness)
        (c := (1 : ℝ)))
  rw [hRep, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hVacuum, hO.coeFn_toLp] with A hVacuumA hOA
  rw [hVacuumA, hOA]
  simp

/-- Orthogonal centering away from a unit Gibbs vacuum subtracts exactly the
squared vacuum coefficient from the squared norm. -/
theorem continuous_compact_oriented_vacuumCenteredL2_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖C.vacuumCenteredL2 f‖ ^ 2 =
      ‖f‖ ^ 2 - (inner ℝ C.gibbsVacuumL2 f) ^ 2 := by
  let v : Lp ℝ 2 C.gibbsMeasure := C.gibbsVacuumL2
  let a : ℝ := inner ℝ v f
  have hvNorm : ‖v‖ = 1 := by
    simpa [v] using continuous_compact_oriented_gibbsVacuumL2_norm C
  have hvInner : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hvNorm]
    norm_num
  have hSymm : inner ℝ f v = a := by
    dsimp [a]
    exact (real_inner_comm f v).symm
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  change ‖f - a • v‖ ^ 2 = ‖f‖ ^ 2 - a ^ 2
  calc
    ‖f - a • v‖ ^ 2 = inner ℝ (f - a • v) (f - a • v) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ f f - a ^ 2 := by
      simp only [inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hSymm, hvInner]
      ring
    _ = ‖f‖ ^ 2 - a ^ 2 := by
      rw [real_inner_self_eq_norm_sq]

/-- On the bounded-continuous core, Gibbs variance is exactly the squared norm
of orthogonal centering away from the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_gibbsVarianceBCF_eq_vacuumCentered_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsVarianceBCF O =
      ‖C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let hO : MemLp O 2 C.gibbsMeasure :=
    continuous_compact_oriented_bcf_memLp_two C O
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsVarianceBCF
  rw [ProbabilityTheory.variance_eq_sub hO,
    continuous_compact_oriented_vacuumCenteredL2_norm_sq,
    continuous_compact_oriented_gibbsL2RepresentativeBCF_norm_sq_eq_integral_sq,
    continuous_compact_oriented_inner_gibbsVacuumL2_gibbsL2RepresentativeBCF]
  simp only [Pi.pow_apply]

/-- The mean-square difference of two independent Gibbs configurations is twice
the Gibbs variance of the observable. -/
theorem continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_eq_two_mul_variance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsIndependentPairDifferenceEnergyBCF O =
      2 * C.gibbsVarianceBCF O := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ : Measure C.base.Configuration := C.gibbsMeasure
  let hO : MemLp O 2 μ := by
    simpa [μ] using continuous_compact_oriented_bcf_memLp_two C O
  let diff : C.base.Configuration × C.base.Configuration → ℝ :=
    fun z => O z.1 - O z.2
  have hDiff : MemLp diff 2 (μ.prod μ) := by
    dsimp [diff]
    exact (hO.comp_fst μ).sub (hO.comp_snd μ)
  have hOInt : Integrable O μ := hO.integrable one_le_two
  have hMeanZero : ∫ z, diff z ∂(μ.prod μ) = 0 := by
    dsimp [diff]
    rw [integral_sub (hOInt.comp_fst μ) (hOInt.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  have hVarianceIntegral :
      ProbabilityTheory.variance diff (μ.prod μ) =
        ∫ z, (diff z) ^ 2 ∂(μ.prod μ) :=
    ProbabilityTheory.variance_of_integral_eq_zero hDiff.aemeasurable hMeanZero
  have hVarianceProd :=
    ProbabilityTheory.variance_add_prod (μ := μ) (ν := μ) hO hO.neg
  calc
    C.gibbsIndependentPairDifferenceEnergyBCF O =
        ProbabilityTheory.variance diff (μ.prod μ) := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.gibbsIndependentPairDifferenceEnergyBCF
      change (∫ z, (diff z) ^ 2 ∂(μ.prod μ)) = _
      exact hVarianceIntegral.symm
    _ = ProbabilityTheory.variance O μ +
        ProbabilityTheory.variance (fun A => -O A) μ := by
      simpa [diff, sub_eq_add_neg] using hVarianceProd
    _ = 2 * ProbabilityTheory.variance O μ := by
      rw [ProbabilityTheory.variance_fun_neg]
      ring
    _ = 2 * C.gibbsVarianceBCF O := by
      rfl

/-- Coupling-ready global variance identity: the independent Gibbs pair
mean-square difference equals twice the squared centered Gibbs `L²` norm. -/
theorem continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_eq_two_mul_centered_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsIndependentPairDifferenceEnergyBCF O =
      2 * ‖C.vacuumCenteredL2 (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  rw [continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_eq_two_mul_variance,
    continuous_compact_oriented_gibbsVarianceBCF_eq_vacuumCentered_norm_sq]

end

end MathlibAnalytic
end MGAP4D
