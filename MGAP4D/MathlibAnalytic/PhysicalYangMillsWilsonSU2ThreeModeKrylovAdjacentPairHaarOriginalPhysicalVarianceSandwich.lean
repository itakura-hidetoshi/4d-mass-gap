import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUniformWilsonChangeOfMeasureDeviation
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-DF: genuine original Wilson vs pair-Haar finite-volume variance comparison

DE proved ONE density sandwich, uniform in every nonnegative measurable
observable and all squared real deviations, on the ACTUAL original physical
Wilson ground-state joint probability versus original independent pair-Haar.

The two probability laws have DIFFERENT global means. It is incorrect to
identify their centered variances by simply equating these means. We use
instead the best-constant characterization of squared variance: for either
probability, its variance is no larger than its mean squared deviation
from ANY fixed real center.

Apply DE's uniform quadratic comparison at the TRUE Wilson mean for
the lower bound, and at the TRUE pair-Haar mean for the upper bound.
Bounded strongly measurable physical observables are genuinely in L²
for both original probability laws. These finite-volume bounds hold
SIMULTANEOUSLY for ALL such functions, with one m>0 and M>=0 independent
of the observable or centering constant.

This establishes a quantitative finite-volume variance comparison,
NOT yet a lower bound for the ORIGINAL Wilson Riesz/Dirichlet quadratic
by the actual pair-Haar coordinate residual energy. In particular
the density constants may depend on volume H, group rank N and beta,
and this does not establish a volume-uniform or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- On any genuine probability space, variance is the least squared
deviation from a real constant, and hence bounded by the deviation
about any chosen constant. This is a theorem of the original probability,
not a pair-Haar / Wilson mean-identification assertion. -/
private theorem p4Q2DF_variance_le_anyCenteredSquare
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : AEStronglyMeasurable F μ) (c : ℝ) :
    variance F μ ≤ ∫ z, (F z - c) ^ 2 ∂μ := by
  have h := variance_le_expectation_sq (hF.sub_const c)
  rw [variance_sub_const hF c] at h
  simpa only [Pi.pow_apply] using h

section OriginalWilson
variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muWilson" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta

/-- All actual finite-volume original Wilson variances lie between the
pair-Haar variances times ONE universal density-floor and ceiling,
for every bounded strongly measurable original joint observable.
Both measures, all constants and both genuine means are physical. -/
theorem p4Q2DF_originalWilsonJoint_allBoundedVariance_uniform_sandwich :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∀ (F : Joint → ℝ) (hF : StronglyMeasurable F)
        (B : ℝ) (hB : ∀ z, ‖F z‖ ≤ B),
        m * variance F muPair ≤ variance F muWilson ∧
        variance F muWilson ≤ M * variance F muPair := by
  letI : IsProbabilityMeasure muPair := by infer_instance
  letI : IsProbabilityMeasure muWilson :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  obtain ⟨m, M, hm, hAll⟩ :=
    p4Q2DE_originalWilsonJoint_allSquaredDeviations_uniform_sandwich
      H N hN beta hbeta
  have hOne := (hAll (fun _ : Joint => (1 : ℝ)) stronglyMeasurable_const (0 : ℝ))
  have hMnonneg : 0 ≤ M := by
    have hMeasureOne :
        (1 : ENNReal) ≤ ENNReal.ofReal M := by
      simpa using hOne.2
    by_contra hneg
    have hnonpos : M ≤ 0 := le_of_lt (lt_of_not_ge hneg)
    rw [ENNReal.ofReal_of_nonpos hnonpos] at hMeasureOne
    norm_num at hMeasureOne
  refine ⟨m, M, hm, hMnonneg, ?_⟩
  intro F hF B hB
  have hSubSm (c : ℝ) :
      StronglyMeasurable (fun z : Joint => F z - c) :=
    hF.sub stronglyMeasurable_const
  have hSubBound (c : ℝ) (z : Joint) :
      ‖F z - c‖ ≤ B + ‖c‖ := by
    calc
      ‖F z - c‖ ≤ ‖F z‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ B + ‖c‖ := add_le_add_right (hB z) _
  have hSqMeas (c : ℝ) :
      Measurable (fun z : Joint => (F z - c) ^ 2) :=
    ((hF.measurable.sub measurable_const).pow_const 2)
  have hIntPair (c : ℝ) :
      Integrable (fun z : Joint => (F z - c) ^ 2) muPair := by
    apply (memLp_two_iff_integrable_sq
      (hSubSm c).aestronglyMeasurable).mp
    exact MemLp.of_bound (hSubSm c).aestronglyMeasurable
      (B + ‖c‖) (Filter.Eventually.of_forall (hSubBound c))
  have hIntWilson (c : ℝ) :
      Integrable (fun z : Joint => (F z - c) ^ 2) muWilson := by
    apply (memLp_two_iff_integrable_sq
      (hSubSm c).aestronglyMeasurable).mp
    exact MemLp.of_bound (hSubSm c).aestronglyMeasurable
      (B + ‖c‖) (Filter.Eventually.of_forall (hSubBound c))
  have hNonneg (c : ℝ) (μ : Measure Joint) :
      0 ≤ᵐ[μ] (fun z : Joint => (F z - c) ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg (F z - c))
  have hPairEq (c : ℝ) :
      (∫ z : Joint, (F z - c) ^ 2 ∂muPair) =
        ENNReal.toReal
          (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muPair) :=
    integral_eq_lintegral_of_nonneg_ae (hNonneg c muPair)
      (hSqMeas c).aestronglyMeasurable
  have hWilsonEq (c : ℝ) :
      (∫ z : Joint, (F z - c) ^ 2 ∂muWilson) =
        ENNReal.toReal
          (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muWilson) :=
    integral_eq_lintegral_of_nonneg_ae (hNonneg c muWilson)
      (hSqMeas c).aestronglyMeasurable
  have hFinPair (c : ℝ) :
      (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muPair) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hSqMeas c).aestronglyMeasurable (hNonneg c muPair)).2
        (hIntPair c)
  have hFinWilson (c : ℝ) :
      (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muWilson) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hSqMeas c).aestronglyMeasurable (hNonneg c muWilson)).2
        (hIntWilson c)
  have hLowerReal (c : ℝ) :
      m * (∫ z : Joint, (F z - c) ^ 2 ∂muPair) ≤
        (∫ z : Joint, (F z - c) ^ 2 ∂muWilson) := by
    have h := ENNReal.toReal_mono (hFinWilson c) (hAll F hF c).1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le] at h
    calc
      m * (∫ z : Joint, (F z - c) ^ 2 ∂muPair) =
        m * ENNReal.toReal
          (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muPair) := by
            rw [hPairEq]
      _ ≤ ENNReal.toReal
          (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muWilson) := h
      _ = (∫ z : Joint, (F z - c) ^ 2 ∂muWilson) :=
        (hWilsonEq c).symm
  have hUpperReal (c : ℝ) :
      (∫ z : Joint, (F z - c) ^ 2 ∂muWilson) ≤
        M * (∫ z : Joint, (F z - c) ^ 2 ∂muPair) := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hFinPair c))
      (hAll F hF c).2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMnonneg] at h
    calc
      (∫ z : Joint, (F z - c) ^ 2 ∂muWilson) =
        ENNReal.toReal
          (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muWilson) := hWilsonEq c
      _ ≤ M * ENNReal.toReal
          (∫⁻ z : Joint, ENNReal.ofReal ((F z - c) ^ 2) ∂muPair) := h
      _ = M * (∫ z : Joint, (F z - c) ^ 2 ∂muPair) := by
        rw [hPairEq]
  constructor
  · calc
      m * variance F muPair ≤
          m * (∫ z : Joint,
            (F z - (∫ t : Joint, F t ∂muWilson)) ^ 2 ∂muPair) :=
        mul_le_mul_of_nonneg_left
          (p4Q2DF_variance_le_anyCenteredSquare muPair F
            hF.aestronglyMeasurable (∫ t : Joint, F t ∂muWilson)) hm.le
      _ ≤ ∫ z : Joint,
          (F z - (∫ t : Joint, F t ∂muWilson)) ^ 2 ∂muWilson :=
        hLowerReal (∫ t : Joint, F t ∂muWilson)
      _ = variance F muWilson := by
        rw [variance_eq_integral hF.measurable.aemeasurable]
  · calc
      variance F muWilson ≤
          ∫ z : Joint,
            (F z - (∫ t : Joint, F t ∂muPair)) ^ 2 ∂muWilson :=
        p4Q2DF_variance_le_anyCenteredSquare muWilson F
          hF.aestronglyMeasurable (∫ t : Joint, F t ∂muPair)
      _ ≤ M * (∫ z : Joint,
          (F z - (∫ t : Joint, F t ∂muPair)) ^ 2 ∂muPair) :=
        hUpperReal (∫ t : Joint, F t ∂muPair)
      _ = M * variance F muPair := by
        rw [variance_eq_integral hF.measurable.aemeasurable]

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
