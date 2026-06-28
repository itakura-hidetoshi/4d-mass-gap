import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkGibbsIntegral

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- The global real Gibbs density is strictly positive. -/
theorem continuous_compact_oriented_gibbsDensityReal_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) :
    0 < C.gibbsDensityReal A := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsDensityReal
  exact div_pos (Real.exp_pos _)
    (compact_oriented_partitionFunction_pos C.base)

/-- Every exact one-link real conditional density is strictly positive. -/
theorem continuous_compact_oriented_singleLinkConditionalDensityReal_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    0 < C.singleLinkConditionalDensityReal A target g := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact div_pos (Real.exp_pos _)
    (continuous_compact_oriented_singleLinkPartitionFunction_pos
      C A target)

/-- Joint density of an old selected-link value, a newly sampled value, and
all off-link variables. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkJointDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (g h : C.base.Gauge)
    (Aoff : C.base.OffLinkConfiguration target) : ℝ≥0∞ :=
  C.singleLinkCoordinateGibbsDensity target (g, Aoff) *
    C.singleLinkConditionalDensity target
      (C.base.singleLinkAssemble target g Aoff) h

/-- The compact one-link joint transition density is symmetric under exchange
of the old and new selected-link values. -/
theorem continuous_compact_oriented_singleLinkJointDensity_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (g h : C.base.Gauge)
    (Aoff : C.base.OffLinkConfiguration target) :
    C.singleLinkJointDensity target g h Aoff =
      C.singleLinkJointDensity target h g Aoff := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkJointDensity
  rw [continuous_compact_oriented_singleLinkCoordinateGibbsDensity_apply,
    continuous_compact_oriented_singleLinkCoordinateGibbsDensity_apply]
  change
    ENNReal.ofReal
        (C.gibbsDensityReal
          (C.base.singleLinkAssemble target g Aoff)) *
      ENNReal.ofReal
        (C.singleLinkConditionalDensityReal
          (C.base.singleLinkAssemble target g Aoff) target h) =
    ENNReal.ofReal
        (C.gibbsDensityReal
          (C.base.singleLinkAssemble target h Aoff)) *
      ENNReal.ofReal
        (C.singleLinkConditionalDensityReal
          (C.base.singleLinkAssemble target h Aoff) target g)
  rw [← ENNReal.ofReal_mul
      (le_of_lt (continuous_compact_oriented_gibbsDensityReal_pos C _)),
    ← ENNReal.ofReal_mul
      (le_of_lt (continuous_compact_oriented_gibbsDensityReal_pos C _))]
  apply congrArg ENNReal.ofReal
  simpa [compact_oriented_replaceLink_singleLinkAssemble] using
    continuous_compact_oriented_singleLink_density_detailedBalance
      C (C.base.singleLinkAssemble target 1 Aoff) target g h

end

end MathlibAnalytic
end MGAP4D
