import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapAnchoredWeights
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Right residual density normalized by the common unmatched mass.  When the
unmatched mass vanishes, normalized Haar is used as an explicit probability
fallback. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge)
    (h : C.base.Gauge) : ℝ≥0∞ :=
  if C.configurationPairConditionalResidualMass target w.1 = 0 then 1
  else
    (C.configurationPairConditionalResidualMass target w.1)⁻¹ *
      C.configurationPairConditionalRightResidualDensity target w.1 h

/-- The normalized right-residual density is jointly measurable in the
background pair, the left anchor, and the output target value. -/
theorem measurable_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualDensity_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (Function.uncurry
      (C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
        target)) := by
  let δ := C.configurationPairConditionalResidualMass target
  have hδ : Measurable δ :=
    continuous_compact_oriented_configurationPairConditionalResidualMass_measurable
      C target
  have hδInput : Measurable
      (fun x : (((C.base.Configuration × C.base.Configuration) × C.base.Gauge) ×
          C.base.Gauge) => δ x.1.1) :=
    hδ.comp (measurable_fst.comp measurable_fst)
  have hZero : MeasurableSet
      {x : (((C.base.Configuration × C.base.Configuration) × C.base.Gauge) ×
          C.base.Gauge) | δ x.1.1 = 0} :=
    hδInput (measurableSet_singleton 0)
  have hRightInput : Measurable
      (fun x : (((C.base.Configuration × C.base.Configuration) × C.base.Gauge) ×
          C.base.Gauge) => (x.1.1, x.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hRight : Measurable
      (fun x : (((C.base.Configuration × C.base.Configuration) × C.base.Gauge) ×
          C.base.Gauge) =>
        C.configurationPairConditionalRightResidualDensity target x.1.1 x.2) :=
    (measurable_compact_oriented_configurationPairConditionalRightResidualDensity_uncurry
      C target).comp hRightInput
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualDensity
  change Measurable
    (fun x : (((C.base.Configuration × C.base.Configuration) × C.base.Gauge) ×
        C.base.Gauge) =>
      if δ x.1.1 = 0 then 1 else δ x.1.1⁻¹ *
        C.configurationPairConditionalRightResidualDensity target x.1.1 x.2)
  exact Measurable.ite hZero measurable_const (hδInput.inv.mul hRight)

/-- Probability measure used by the residual branch of the anchored transition.
It is normalized Haar on a zero-residual fiber and the normalized right residual
law otherwise. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    Measure C.base.Gauge :=
  if C.configurationPairConditionalResidualMass target w.1 = 0 then
    normalizedCompactHaar C.base.Gauge
  else
    (C.configurationPairConditionalResidualMass target w.1)⁻¹ •
      C.singleLinkConditionalRightResidualMeasure w.1.1 w.1.2 target

/-- The explicit normalized density realizes the named normalized
right-residual probability measure. -/
theorem continuous_compact_oriented_withDensity_anchoredNormalizedRightResidualDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    (normalizedCompactHaar C.base.Gauge).withDensity
        (C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
          target w) =
      C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
        target w := by
  let δ := C.configurationPairConditionalResidualMass target w.1
  by_cases hδ : δ = 0
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualDensity,
      ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualMeasure,
      δ, hδ]
  · have hRightMeas : Measurable
        (C.configurationPairConditionalRightResidualDensity target w.1) := by
      simpa [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalRightResidualDensity]
        using continuous_compact_oriented_singleLinkConditionalRightResidualDensity_measurable
          C w.1.1 w.1.2 target
    have hSmul := MeasureTheory.withDensity_smul
      (μ := normalizedCompactHaar C.base.Gauge) δ⁻¹ hRightMeas
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualDensity,
      ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualMeasure,
      ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalRightResidualDensity,
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualMeasure,
      Pi.smul_apply, smul_eq_mul, δ, hδ] using hSmul

/-- The residual-branch fallback measure has total mass one on every fiber. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualMeasure_univ
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
        target w univ = 1 := by
  let δ := C.configurationPairConditionalResidualMass target w.1
  by_cases hδ : δ = 0
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualMeasure,
      δ, hδ]
  · rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredNormalizedRightResidualMeasure,
      if_neg hδ, Measure.smul_apply, smul_eq_mul]
    rw [continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
      C w.1.1 w.1.2 target]
    exact ENNReal.inv_mul_cancel hδ
      (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
        C w.1.1 w.1.2 target)

/-- Diagonal part of the anchored transition: retain the left anchor with the
pointwise common-overlap probability. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalTransitionKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel ((C.base.Configuration × C.base.Configuration) × C.base.Gauge)
      C.base.Gauge :=
  Kernel.withDensity
    (Kernel.deterministic (fun w => w.2) measurable_snd)
    (fun w (_ : C.base.Gauge) =>
      C.configurationPairConditionalAnchoredDiagonalWeight target w)

/-- Residual part of the anchored transition: sample the normalized right
residual law with the pointwise left-residual probability. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualTransitionKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel ((C.base.Configuration × C.base.Configuration) × C.base.Gauge)
      C.base.Gauge :=
  Kernel.withDensity
    (Kernel.const
      ((C.base.Configuration × C.base.Configuration) × C.base.Gauge)
      (normalizedCompactHaar C.base.Gauge))
    (fun w h =>
      C.configurationPairConditionalAnchoredResidualWeight target w *
        C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
          target w h)

/-- The diagonal transition fiber is exactly a weighted Dirac mass at the left
anchor. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalTransitionKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredDiagonalTransitionKernel target w =
      C.configurationPairConditionalAnchoredDiagonalWeight target w •
        Measure.dirac w.2 := by
  have hWeight : Measurable (Function.uncurry
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        fun _ : C.base.Gauge =>
          C.configurationPairConditionalAnchoredDiagonalWeight target w)) := by
    simpa [Function.uncurry] using
      (measurable_compact_oriented_configurationPairConditionalAnchoredDiagonalWeight
        C target).comp measurable_fst
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredDiagonalTransitionKernel,
    Kernel.withDensity_apply _ hWeight,
    Kernel.deterministic_apply measurable_snd,
    MeasureTheory.withDensity_const]

/-- The residual transition fiber is the residual branch probability times the
normalized right-residual fallback measure. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredResidualTransitionKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredResidualTransitionKernel target w =
      C.configurationPairConditionalAnchoredResidualWeight target w •
        C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
          target w := by
  have hDensity : Measurable (Function.uncurry
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        fun h : C.base.Gauge =>
          C.configurationPairConditionalAnchoredResidualWeight target w *
            C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
              target w h)) := by
    exact
      ((measurable_compact_oriented_configurationPairConditionalAnchoredResidualWeight
          C target).comp measurable_fst).mul
        (measurable_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualDensity_uncurry
          C target)
  have hNormalized : Measurable
      (C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
        target w) :=
    Measurable.of_uncurry_left
      (measurable_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualDensity_uncurry
        C target)
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredResidualTransitionKernel,
    Kernel.withDensity_apply _ hDensity, Kernel.const_apply]
  calc
    (normalizedCompactHaar C.base.Gauge).withDensity
        (fun h =>
          C.configurationPairConditionalAnchoredResidualWeight target w *
            C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
              target w h) =
      C.configurationPairConditionalAnchoredResidualWeight target w •
        (normalizedCompactHaar C.base.Gauge).withDensity
          (C.configurationPairConditionalAnchoredNormalizedRightResidualDensity
            target w) := by
              simpa [Pi.smul_apply, smul_eq_mul] using
                (MeasureTheory.withDensity_smul
                  (μ := normalizedCompactHaar C.base.Gauge)
                  (C.configurationPairConditionalAnchoredResidualWeight target w)
                  hNormalized)
    _ = C.configurationPairConditionalAnchoredResidualWeight target w •
        C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
          target w := by
            rw [continuous_compact_oriented_withDensity_anchoredNormalizedRightResidualDensity]

/-- Explicit left-anchored overlap transition kernel. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredOverlapTransitionKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel ((C.base.Configuration × C.base.Configuration) × C.base.Gauge)
      C.base.Gauge :=
  C.configurationPairConditionalAnchoredDiagonalTransitionKernel target +
    C.configurationPairConditionalAnchoredResidualTransitionKernel target

/-- Every anchored transition fiber is the exact diagonal/residual mixture. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge) :
    C.configurationPairConditionalAnchoredOverlapTransitionKernel target w =
      C.configurationPairConditionalAnchoredDiagonalWeight target w •
          Measure.dirac w.2 +
        C.configurationPairConditionalAnchoredResidualWeight target w •
          C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
            target w := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredOverlapTransitionKernel,
    Kernel.add_apply,
    continuous_compact_oriented_configurationPairConditionalAnchoredDiagonalTransitionKernel_apply,
    continuous_compact_oriented_configurationPairConditionalAnchoredResidualTransitionKernel_apply]

/-- The explicit left-anchored overlap transition is Markov on every input,
including the zero-residual fallback fibers. -/
instance continuousCompactOriented_configurationPairConditionalAnchoredOverlapTransitionKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel
      (C.configurationPairConditionalAnchoredOverlapTransitionKernel target) :=
  ⟨fun w => by
    constructor
    rw [continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernel_apply,
      Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      continuous_compact_oriented_configurationPairConditionalAnchoredNormalizedRightResidualMeasure_univ,
      smul_eq_mul]
    simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ,
      Set.indicator_of_mem, mul_one]
    exact continuous_compact_oriented_configurationPairConditionalAnchoredWeights_add
      C target w⟩

end

end MathlibAnalytic
end MGAP4D
