import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryProkhorovLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEuclideanTimeTranslationLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalTemporalAction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding) where
  translate : ℝ → Homeomorph E.PhysicalConfiguration E.PhysicalConfiguration
  translate_zero_apply : ∀ A, translate 0 A = A
  translate_add_apply : ∀ s t A,
    translate (s + t) A = translate s (translate t A)
  latticeTranslate : ∀ n, ℝ →
    (E.system n).base.Configuration → (E.system n).base.Configuration
  latticeTranslate_measurable : ∀ n t,
    Measurable (latticeTranslate n t)
  latticeGibbs_map_eq_self : ∀ n t,
    Measure.map (latticeTranslate n t) (E.system n).gibbsMeasure =
      (E.system n).gibbsMeasure
  interpolate_equivariant : ∀ n t U,
    E.interpolate n (latticeTranslate n t U) =
      translate t (E.interpolate n U)

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

theorem translate_comp_interpolate
    (A : E.PhysicalTemporalAction) (n : ℕ) (t : ℝ) :
    A.translate t ∘ E.interpolate n =
      E.interpolate n ∘ A.latticeTranslate n t := by
  funext U
  exact (A.interpolate_equivariant n t U).symm

theorem embeddedMeasure_toMeasure_map_eq_self
    (A : E.PhysicalTemporalAction) (n : ℕ) (t : ℝ) :
    Measure.map (A.translate t)
        (ProbabilityMeasure.toMeasure
          (E.toLatticeEmbedding.embeddedMeasure n)) =
      ProbabilityMeasure.toMeasure
        (E.toLatticeEmbedding.embeddedMeasure n) := by
  change
    Measure.map (A.translate t)
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure
  calc
    Measure.map (A.translate t)
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map (A.translate t ∘ E.interpolate n)
        (E.system n).gibbsMeasure :=
      Measure.map_map (A.translate t).continuous.measurable
        (E.interpolate_measurable n)
    _ = Measure.map
        (E.interpolate n ∘ A.latticeTranslate n t)
        (E.system n).gibbsMeasure := by
      rw [A.translate_comp_interpolate n t]
    _ = Measure.map (E.interpolate n)
        (Measure.map (A.latticeTranslate n t)
          (E.system n).gibbsMeasure) :=
      (Measure.map_map (E.interpolate_measurable n)
        (A.latticeTranslate_measurable n t)).symm
    _ = Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
      rw [A.latticeGibbs_map_eq_self]

theorem embeddedMeasure_map_eq_self
    (A : E.PhysicalTemporalAction) (n : ℕ) (t : ℝ) :
    (E.toLatticeEmbedding.embeddedMeasure n).map
        (A.translate t).continuous.measurable.aemeasurable =
      E.toLatticeEmbedding.embeddedMeasure n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  exact A.embeddedMeasure_toMeasure_map_eq_self n t

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalTemporalAction

structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeTemporalCompatibility
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (A : E.PhysicalTemporalAction) where
  gauge_commute : ∀ t g X,
    A.translate t (G.action g X) = G.action g (A.translate t X)

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeTemporalCompatibility

noncomputable def toEuclideanTimeTranslationLimit
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {A : E.PhysicalTemporalAction}
    (C : E.GaugeTemporalCompatibility G A)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit
      (G.toSymmetryLimit L) where
  translate := A.translate
  translate_zero_apply := A.translate_zero_apply
  translate_add_apply := A.translate_add_apply
  gauge_commute := C.gauge_commute
  approximatingInvariant n t :=
    A.embeddedMeasure_map_eq_self (L.subsequence n) t

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeTemporalCompatibility

end

end MathlibAnalytic
end MGAP4D
