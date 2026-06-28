import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Scale-separated temporal dynamics.

At scale `n`, exact dynamics is indexed by `ℤ`, while `latticeTime n` embeds
those steps additively into physical real time. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding) where
  physicalTranslate : ℝ → Homeomorph E.PhysicalConfiguration E.PhysicalConfiguration
  physicalTranslate_zero_apply : ∀ X, physicalTranslate 0 X = X
  physicalTranslate_add_apply : ∀ s t X,
    physicalTranslate (s + t) X = physicalTranslate s (physicalTranslate t X)
  latticeTime : ∀ n, ℤ →+ ℝ
  latticeTranslate : ∀ n, ℤ →
    (E.system n).base.Configuration → (E.system n).base.Configuration
  latticeTranslate_measurable : ∀ n k, Measurable (latticeTranslate n k)
  latticeTranslate_zero_apply : ∀ n U, latticeTranslate n 0 U = U
  latticeTranslate_add_apply : ∀ n k l U,
    latticeTranslate n (k + l) U =
      latticeTranslate n k (latticeTranslate n l U)
  latticeGibbs_map_eq_self : ∀ n k,
    Measure.map (latticeTranslate n k) (E.system n).gibbsMeasure =
      (E.system n).gibbsMeasure
  interpolate_equivariant : ∀ n k U,
    E.interpolate n (latticeTranslate n k U) =
      physicalTranslate (latticeTime n k) (E.interpolate n U)

end

end MathlibAnalytic
end MGAP4D
