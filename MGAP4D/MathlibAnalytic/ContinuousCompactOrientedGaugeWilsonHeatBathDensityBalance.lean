import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathKernelIdempotent

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Real density of the global compact oriented Wilson Gibbs law with respect
to product normalized Haar measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsDensityReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) : ℝ :=
  Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction

/-- Real density of the exact one-link Haar conditional law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  C.singleLinkBoltzmannFactor A target g /
    C.singleLinkPartitionFunction A target

/-- The one-link conditional partition function is unchanged by replacing the
same physical link. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkPartitionFunction
        (C.base.replaceLink A target g) target =
      C.singleLinkPartitionFunction A target := by
  apply
    continuous_compact_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
  intro e he
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, he]

/-- Fiberwise pointwise detailed balance: exchanging the old and newly sampled
link values preserves the product of global Gibbs density and conditional Haar
density. -/
theorem continuous_compact_oriented_singleLink_density_detailedBalance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g h : C.base.Gauge) :
    C.gibbsDensityReal (C.base.replaceLink A target g) *
        C.singleLinkConditionalDensityReal
          (C.base.replaceLink A target g) target h =
      C.gibbsDensityReal (C.base.replaceLink A target h) *
        C.singleLinkConditionalDensityReal
          (C.base.replaceLink A target h) target g := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsDensityReal
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  rw [continuous_compact_oriented_singleLinkPartitionFunction_replaceLink
      C A target g,
    continuous_compact_oriented_singleLinkPartitionFunction_replaceLink
      C A target h,
    compact_oriented_replaceLink_replaceLink,
    compact_oriented_replaceLink_replaceLink]
  ring

end

end MathlibAnalytic
end MGAP4D
