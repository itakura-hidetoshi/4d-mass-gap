import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDiscreteTemporalActionAdditive
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDiscreteTemporalActionInverse

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- Every embedded finite-volume law is invariant at every realizable lattice
time. -/
theorem embeddedMeasure_toMeasure_map_latticeTime_eq_self
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ) :
    Measure.map (A.physicalTranslate (A.latticeTime n k))
        (ProbabilityMeasure.toMeasure
          (E.toLatticeEmbedding.embeddedMeasure n)) =
      ProbabilityMeasure.toMeasure
        (E.toLatticeEmbedding.embeddedMeasure n) := by
  change
    Measure.map (A.physicalTranslate (A.latticeTime n k))
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure
  calc
    Measure.map (A.physicalTranslate (A.latticeTime n k))
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map
        (A.physicalTranslate (A.latticeTime n k) ∘ E.interpolate n)
        (E.system n).gibbsMeasure :=
      Measure.map_map
        (A.physicalTranslate (A.latticeTime n k)).continuous.measurable
        (E.interpolate_measurable n)
    _ = Measure.map (E.interpolate n ∘ A.latticeTranslate n k)
        (E.system n).gibbsMeasure := by
      rw [A.physicalTranslate_latticeTime_comp_interpolate n k]
    _ = Measure.map (E.interpolate n)
        (Measure.map (A.latticeTranslate n k) (E.system n).gibbsMeasure) :=
      (Measure.map_map (E.interpolate_measurable n)
        (A.latticeTranslate_measurable n k)).symm
    _ = Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
      rw [A.latticeGibbs_map_eq_self]

/-- Probability-measure form of invariance at exact scale-dependent times. -/
theorem embeddedMeasure_map_latticeTime_eq_self
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ) :
    (E.toLatticeEmbedding.embeddedMeasure n).map
        (A.physicalTranslate (A.latticeTime n k)).continuous.measurable.aemeasurable =
      E.toLatticeEmbedding.embeddedMeasure n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  exact A.embeddedMeasure_toMeasure_map_latticeTime_eq_self n k

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D
