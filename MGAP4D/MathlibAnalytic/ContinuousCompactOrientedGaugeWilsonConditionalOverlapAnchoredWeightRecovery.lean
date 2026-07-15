import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapAnchoredCouplingMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The exact ENNReal one-link conditional density is pointwise nonzero. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_ne_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g ≠ 0 := by
  rw [continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real]
  apply (ENNReal.ofReal_pos.mpr ?_).ne'
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact div_pos (Real.exp_pos _)
    (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)

/-- The exact ENNReal one-link conditional density is pointwise finite. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_ne_top
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g ≠ ∞ := by
  rw [continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real]
  exact ENNReal.ofReal_ne_top

/-- At a fixed background pair, common overlap plus left residual is the exact
left conditional density in the configuration-pair notation. -/
theorem continuous_compact_oriented_configurationPairConditionalTotalLeftDensity_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.configurationPairConditionalOverlapDensity target (A, B) g +
        C.configurationPairConditionalLeftResidualDensity target (A, B) g =
      C.singleLinkConditionalDensity target A g := by
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualDensity]
    using
      continuous_compact_oriented_singleLinkConditionalOverlapDensity_add_leftResidual
        C A B target g

/-- Multiplying the exact left conditional density by the anchored diagonal
weight recovers the common overlap density pointwise. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mul_anchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g *
        C.configurationPairConditionalAnchoredDiagonalWeight target ((A, B), g) =
      C.singleLinkConditionalOverlapDensity A B target g := by
  have hTotal :=
    continuous_compact_oriented_configurationPairConditionalTotalLeftDensity_eq
      C A B target g
  have h0 :
      C.configurationPairConditionalOverlapDensity target (A, B) g +
          C.configurationPairConditionalLeftResidualDensity target (A, B) g ≠ 0 := by
    rw [hTotal]
    exact continuous_compact_oriented_singleLinkConditionalDensity_ne_zero
      C A target g
  have hTop :
      C.configurationPairConditionalOverlapDensity target (A, B) g +
          C.configurationPairConditionalLeftResidualDensity target (A, B) g ≠ ∞ := by
    rw [hTotal]
    exact continuous_compact_oriented_singleLinkConditionalDensity_ne_top
      C A target g
  rw [← hTotal]
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity]
    using
      continuous_compact_oriented_totalLeftDensity_mul_anchoredDiagonalWeight
        C target ((A, B), g) h0 hTop

/-- Multiplying the exact left conditional density by the anchored residual
weight recovers the left residual density pointwise. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mul_anchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g *
        C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g) =
      C.singleLinkConditionalLeftResidualDensity A B target g := by
  have hTotal :=
    continuous_compact_oriented_configurationPairConditionalTotalLeftDensity_eq
      C A B target g
  have h0 :
      C.configurationPairConditionalOverlapDensity target (A, B) g +
          C.configurationPairConditionalLeftResidualDensity target (A, B) g ≠ 0 := by
    rw [hTotal]
    exact continuous_compact_oriented_singleLinkConditionalDensity_ne_zero
      C A target g
  have hTop :
      C.configurationPairConditionalOverlapDensity target (A, B) g +
          C.configurationPairConditionalLeftResidualDensity target (A, B) g ≠ ∞ := by
    rw [hTotal]
    exact continuous_compact_oriented_singleLinkConditionalDensity_ne_top
      C A target g
  rw [← hTotal]
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualDensity]
    using
      continuous_compact_oriented_totalLeftDensity_mul_anchoredResidualWeight
        C target ((A, B), g) h0 hTop

/-- Reweighting the exact left conditional law by the anchored diagonal branch
probability gives exactly the common overlap measure. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_withDensity_anchoredDiagonalWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (C.singleLinkConditionalMeasure A target).withDensity
        (fun g : C.base.Gauge =>
          C.configurationPairConditionalAnchoredDiagonalWeight target ((A, B), g)) =
      C.singleLinkConditionalOverlapMeasure A B target := by
  have hDensity : Measurable
      (fun g : C.base.Gauge => C.singleLinkConditionalDensity target A g) :=
    continuous_compact_oriented_singleLinkConditionalDensity_measurable
      C A target
  have hWeight : Measurable
      (fun g : C.base.Gauge =>
        C.configurationPairConditionalAnchoredDiagonalWeight target ((A, B), g)) :=
    (measurable_compact_oriented_configurationPairConditionalAnchoredDiagonalWeight
      C target).comp (measurable_const.prodMk measurable_id)
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapMeasure
  rw [← withDensity_mul (normalizedCompactHaar C.base.Gauge) hDensity hWeight]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun g =>
    continuous_compact_oriented_singleLinkConditionalDensity_mul_anchoredDiagonalWeight
      C A B target g

/-- Reweighting the exact left conditional law by the anchored residual branch
probability gives exactly the left residual measure. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_withDensity_anchoredResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (C.singleLinkConditionalMeasure A target).withDensity
        (fun g : C.base.Gauge =>
          C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g)) =
      C.singleLinkConditionalLeftResidualMeasure A B target := by
  have hDensity : Measurable
      (fun g : C.base.Gauge => C.singleLinkConditionalDensity target A g) :=
    continuous_compact_oriented_singleLinkConditionalDensity_measurable
      C A target
  have hWeight : Measurable
      (fun g : C.base.Gauge =>
        C.configurationPairConditionalAnchoredResidualWeight target ((A, B), g)) :=
    (measurable_compact_oriented_configurationPairConditionalAnchoredResidualWeight
      C target).comp (measurable_const.prodMk measurable_id)
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualMeasure
  rw [← withDensity_mul (normalizedCompactHaar C.base.Gauge) hDensity hWeight]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun g =>
    continuous_compact_oriented_singleLinkConditionalDensity_mul_anchoredResidualWeight
      C A B target g

end

end MathlibAnalytic
end MGAP4D
