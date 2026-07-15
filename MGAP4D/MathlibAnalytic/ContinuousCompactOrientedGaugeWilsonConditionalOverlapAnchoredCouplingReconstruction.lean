import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapAnchoredWeightRecovery
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace AnchoredMeasureCompProd

/-- A composition-product whose fibers are a measurable weight times the Dirac
mass at the input is the diagonal pushforward of the correspondingly reweighted
input measure. -/
theorem compProd_eq_map_diagonal_of_apply_eq_smul_dirac
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (κ : Kernel α α)
    [SFinite μ]
    [IsSFiniteKernel κ]
    (weight : α → ℝ≥0∞)
    (hκ : ∀ a, κ a = weight a • Measure.dirac a) :
    μ ⊗ₘ κ =
      Measure.map (fun a : α => (a, a)) (μ.withDensity weight) := by
  let diagonal : α → α × α := fun a => (a, a)
  have hDiagonal : Measurable diagonal := measurable_id.prodMk measurable_id
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply hDiagonal hs,
    withDensity_apply _ (hDiagonal hs)]
  simp_rw [hκ, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rw [← lintegral_indicator (hDiagonal hs)]
  apply lintegral_congr
  intro a
  by_cases ha : diagonal a ∈ s
  · have haLeft : a ∈ Prod.mk a ⁻¹' s := ha
    have haDiagonal : a ∈ diagonal ⁻¹' s := ha
    rw [Set.indicator_of_mem haLeft, Set.indicator_of_mem haDiagonal]
    simp
  · have haLeft : a ∉ Prod.mk a ⁻¹' s := ha
    have haDiagonal : a ∉ diagonal ⁻¹' s := ha
    rw [Set.indicator_of_notMem haLeft, Set.indicator_of_notMem haDiagonal]
    simp

/-- A composition-product whose fibers are a measurable input weight times one
fixed output measure is the product of the reweighted input measure and that
fixed output measure. -/
theorem compProd_eq_withDensity_prod_of_apply_eq_smul
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (κ : Kernel α β)
    [SFinite μ]
    [IsSFiniteKernel κ]
    (ν : Measure β)
    [SFinite ν]
    (weight : α → ℝ≥0∞)
    (hWeight : Measurable weight)
    (hκ : ∀ a, κ a = weight a • ν) :
    μ ⊗ₘ κ = (μ.withDensity weight).prod ν := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.prod_apply hs]
  simp_rw [hκ, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_withDensity_eq_lintegral_mul _ hWeight
    (measurable_measure_prodMk_left hs)]
  rfl

end AnchoredMeasureCompProd

/-- The normalized right-residual probability measure at one fixed background
pair, independent of the current left anchor. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredNormalizedRightResidualMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  if C.singleLinkConditionalResidualMass A B target = 0 then
    normalizedCompactHaar C.base.Gauge
  else
    (C.singleLinkConditionalResidualMass A B target)⁻¹ •
      C.singleLinkConditionalRightResidualMeasure A B target

/-- The global anchored normalized right-residual measure specializes to the
fixed-background version and does not depend on the left anchor. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualMeasure_eq_fixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
        target ((A, B), g) =
      C.singleLinkConditionalAnchoredNormalizedRightResidualMeasure A B target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredNormalizedRightResidualMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualMass
  rfl

/-- The fixed normalized right-residual measure has total mass one. -/
theorem continuous_compact_oriented_singleLinkConditionalAnchoredNormalizedRightResidualMeasure_univ
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalAnchoredNormalizedRightResidualMeasure
        A B target univ = 1 := by
  by_cases hδ : C.singleLinkConditionalResidualMass A B target = 0
  · rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredNormalizedRightResidualMeasure,
      if_pos hδ]
    exact measure_univ
  · rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredNormalizedRightResidualMeasure,
      if_neg hδ, Measure.smul_apply, smul_eq_mul,
      continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ]
    exact ENNReal.inv_mul_cancel hδ
      (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
        C A B target)

/-- Diagonal branch of the anchored transition at one fixed pair of background
configurations. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalTransitionKernelAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Kernel C.base.Gauge C.base.Gauge :=
  (C.configurationPairConditionalAnchoredDiagonalTransitionKernel target).comap
    (fun g : C.base.Gauge => (z, g))
    (measurable_const.prodMk measurable_id)

/-- Residual branch of the anchored transition at one fixed pair of background
configurations. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualTransitionKernelAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Kernel C.base.Gauge C.base.Gauge :=
  (C.configurationPairConditionalAnchoredResidualTransitionKernel target).comap
    (fun g : C.base.Gauge => (z, g))
    (measurable_const.prodMk measurable_id)

/-- Fixed-background diagonal fibers are the anchored diagonal weight times the
Dirac mass at the current anchor. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalTransitionKernelAt_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.configurationPairConditionalAnchoredDiagonalTransitionKernelAt
        target (A, B) g =
      C.configurationPairConditionalAnchoredDiagonalWeight target ((A, B), g) •
        Measure.dirac g := by
  change
    C.configurationPairConditionalAnchoredDiagonalTransitionKernel
        target ((A, B), g) = _
  exact
    continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalTransitionKernel_apply
      C target ((A, B), g)

/-- Fixed-background residual fibers are the anchored residual weight times the
fixed normalized right-residual probability measure. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredResidualTransitionKernelAt_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.configurationPairConditionalAnchoredResidualTransitionKernelAt
        target (A, B) g =
      C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g) •
        C.singleLinkConditionalAnchoredNormalizedRightResidualMeasure A B target := by
  change
    C.configurationPairConditionalAnchoredResidualTransitionKernel
        target ((A, B), g) = _
  rw [continuous_compact_oriented_configurationPairConditionalAnchoredResidualTransitionKernel_apply,
    continuous_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualMeasure_eq_fixed]

instance continuousCompactOriented_configurationPairConditionalAnchoredDiagonalTransitionKernelAt_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    IsFiniteKernel
      (C.configurationPairConditionalAnchoredDiagonalTransitionKernelAt target z) := by
  rcases z with ⟨A, B⟩
  refine ⟨⟨1, ENNReal.one_lt_top, fun g => ?_⟩⟩
  rw [continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalTransitionKernelAt_apply]
  simpa [Measure.smul_apply, smul_eq_mul] using
    continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalWeight_le_one
      C target ((A, B), g)

instance continuousCompactOriented_configurationPairConditionalAnchoredResidualTransitionKernelAt_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    IsFiniteKernel
      (C.configurationPairConditionalAnchoredResidualTransitionKernelAt target z) := by
  rcases z with ⟨A, B⟩
  refine ⟨⟨1, ENNReal.one_lt_top, fun g => ?_⟩⟩
  rw [continuous_compact_oriented_configurationPairConditionalAnchoredResidualTransitionKernelAt_apply,
    Measure.smul_apply, smul_eq_mul,
    continuous_compact_oriented_singleLinkConditionalAnchoredNormalizedRightResidualMeasure_univ,
    mul_one]
  exact
    continuous_compact_oriented_configurationPairConditionalAnchoredResidualWeight_le_one
      C target ((A, B), g)

/-- The fixed-background full transition is the sum of its diagonal and residual
branches. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernelAt_eq_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalAnchoredOverlapTransitionKernelAt target z =
      C.configurationPairConditionalAnchoredDiagonalTransitionKernelAt target z +
        C.configurationPairConditionalAnchoredResidualTransitionKernelAt target z := by
  ext g
  rfl

/-- Starting the diagonal branch from the exact left conditional law reconstructs
exactly the diagonal pushforward of the common overlap measure. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_compProd_anchoredDiagonalTransitionKernelAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target ⊗ₘ
        C.configurationPairConditionalAnchoredDiagonalTransitionKernelAt
          target (A, B) =
      Measure.map (fun g : C.base.Gauge => (g, g))
        (C.singleLinkConditionalOverlapMeasure A B target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  calc
    C.singleLinkConditionalMeasure A target ⊗ₘ
        C.configurationPairConditionalAnchoredDiagonalTransitionKernelAt
          target (A, B) =
      Measure.map (fun g : C.base.Gauge => (g, g))
        ((C.singleLinkConditionalMeasure A target).withDensity
          (fun g : C.base.Gauge =>
            C.configurationPairConditionalAnchoredDiagonalWeight target ((A, B), g))) := by
          exact
            AnchoredMeasureCompProd.compProd_eq_map_diagonal_of_apply_eq_smul_dirac
              (C.singleLinkConditionalMeasure A target)
              (C.configurationPairConditionalAnchoredDiagonalTransitionKernelAt
                target (A, B))
              (fun g : C.base.Gauge =>
                C.configurationPairConditionalAnchoredDiagonalWeight target ((A, B), g))
              (continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalTransitionKernelAt_apply
                C A B target)
    _ = Measure.map (fun g : C.base.Gauge => (g, g))
        (C.singleLinkConditionalOverlapMeasure A B target) := by
          rw [continuous_compact_oriented_singleLinkConditionalMeasure_withDensity_anchoredDiagonalWeight]

/-- Starting the residual branch from the exact left conditional law reconstructs
exactly the normalized product of the two residual measures, with zero on the
zero-residual fiber. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_compProd_anchoredResidualTransitionKernelAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target ⊗ₘ
        C.configurationPairConditionalAnchoredResidualTransitionKernelAt
          target (A, B) =
      if C.singleLinkConditionalResidualMass A B target = 0 then
        (0 : Measure (C.base.Gauge × C.base.Gauge))
      else
        (C.singleLinkConditionalResidualMass A B target)⁻¹ •
          ((C.singleLinkConditionalLeftResidualMeasure A B target).prod
            (C.singleLinkConditionalRightResidualMeasure A B target)) := by
  let normalizedRight :=
    C.singleLinkConditionalAnchoredNormalizedRightResidualMeasure A B target
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  letI : IsProbabilityMeasure normalizedRight := by
    constructor
    dsimp [normalizedRight]
    exact
      continuous_compact_oriented_singleLinkConditionalAnchoredNormalizedRightResidualMeasure_univ
        C A B target
  have hWeight : Measurable
      (fun g : C.base.Gauge =>
        C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g)) :=
    (measurable_compact_oriented_configurationPairConditionalAnchoredResidualWeight
      C target).comp (measurable_const.prodMk measurable_id)
  calc
    C.singleLinkConditionalMeasure A target ⊗ₘ
        C.configurationPairConditionalAnchoredResidualTransitionKernelAt
          target (A, B) =
      ((C.singleLinkConditionalMeasure A target).withDensity
        (fun g : C.base.Gauge =>
          C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g))).prod
        normalizedRight := by
          exact
            AnchoredMeasureCompProd.compProd_eq_withDensity_prod_of_apply_eq_smul
              (C.singleLinkConditionalMeasure A target)
              (C.configurationPairConditionalAnchoredResidualTransitionKernelAt
                target (A, B))
              normalizedRight
              (fun g : C.base.Gauge =>
                C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g))
              hWeight
              (continuous_compact_oriented_configurationPairConditionalAnchoredResidualTransitionKernelAt_apply
                C A B target)
    _ = (C.singleLinkConditionalLeftResidualMeasure A B target).prod
        normalizedRight := by
          rw [continuous_compact_oriented_singleLinkConditionalMeasure_withDensity_anchoredResidualWeight]
    _ = if C.singleLinkConditionalResidualMass A B target = 0 then
        (0 : Measure (C.base.Gauge × C.base.Gauge))
      else
        (C.singleLinkConditionalResidualMass A B target)⁻¹ •
          ((C.singleLinkConditionalLeftResidualMeasure A B target).prod
            (C.singleLinkConditionalRightResidualMeasure A B target)) := by
          by_cases hδ : C.singleLinkConditionalResidualMass A B target = 0
          · rw [if_pos hδ]
            have hLeftZero :
                C.singleLinkConditionalLeftResidualMeasure A B target = 0 := by
              apply Measure.measure_univ_eq_zero.mp
              simpa [
                ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass]
                using hδ
            simp [normalizedRight, hLeftZero]
          · rw [if_neg hδ]
            unfold normalizedRight
            rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredNormalizedRightResidualMeasure,
              if_neg hδ, Measure.prod_smul_right]

/-- Integrating the explicit anchored transition against the exact left
conditional law reconstructs exactly the pre-existing overlap coupling measure. -/
theorem continuous_compact_oriented_singleLinkConditionalAnchoredOverlapCouplingMeasure_eq_overlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalAnchoredOverlapCouplingMeasure A B target =
      C.singleLinkConditionalOverlapCouplingMeasure A B target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredOverlapCouplingMeasure
  rw [continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernelAt_eq_add,
    Measure.compProd_add_right,
    continuous_compact_oriented_singleLinkConditionalMeasure_compProd_anchoredDiagonalTransitionKernelAt,
    continuous_compact_oriented_singleLinkConditionalMeasure_compProd_anchoredResidualTransitionKernelAt]
  rfl

/-- Consequently, the second marginal of the anchored joint law is exactly the
right one-link conditional law. -/
theorem continuous_compact_oriented_map_snd_singleLinkConditionalAnchoredOverlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.singleLinkConditionalAnchoredOverlapCouplingMeasure A B target) =
      C.singleLinkConditionalMeasure B target := by
  rw [continuous_compact_oriented_singleLinkConditionalAnchoredOverlapCouplingMeasure_eq_overlapCouplingMeasure]
  exact
    continuous_compact_oriented_map_snd_singleLinkConditionalOverlapCouplingMeasure
      C A B target

end

end MathlibAnalytic
end MGAP4D
