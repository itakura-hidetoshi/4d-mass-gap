import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDenseTemporalApproximation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryProkhorovLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEuclideanTimeTranslationLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Continuum Euclidean-time translation after the discrete-time parameter
boundary has been crossed.

Unlike `PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit`, this
interface does not require every finite approximating law to be invariant under
the exact target real time.  It records only the real continuum action, gauge
commutation, and the continuum probability-law invariance obtained from a
convergent sequence of realizable lattice times. -/
structure PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) where
  translate : ℝ → Homeomorph S.Configuration S.Configuration
  translate_zero_apply : ∀ X, translate 0 X = X
  translate_add_apply : ∀ s t X,
    translate (s + t) X = translate s (translate t X)
  gauge_commute : ∀ t g X,
    translate t (S.action g X) = S.action g (translate t X)
  continuumProbabilityMeasure_map_eq_self : ∀ t,
    S.continuumMeasure.map
        (translate t).continuous.measurable.aemeasurable =
      S.continuumMeasure

namespace PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}

/-- Measure-valued form of continuum time-translation invariance. -/
theorem continuumMeasure_map_eq_self
    (T : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (t : ℝ) :
    Measure.map (T.translate t)
        (S.continuumMeasure : Measure S.Configuration) =
      (S.continuumMeasure : Measure S.Configuration) := by
  have h := congrArg ProbabilityMeasure.toMeasure
    (T.continuumProbabilityMeasure_map_eq_self t)
  simpa only [ProbabilityMeasure.toMeasure_map] using h

/-- The older stronger interface, when available, forgets to the continuum-only
real-time action. -/
noncomputable def ofEuclideanTimeTranslationLimit
    (T : PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit S) :
    PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S where
  translate := T.translate
  translate_zero_apply := T.translate_zero_apply
  translate_add_apply := T.translate_add_apply
  gauge_commute := T.gauge_commute
  continuumProbabilityMeasure_map_eq_self :=
    T.continuumProbabilityMeasure_map_eq_self

end PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation

/-- Compatibility of a physical gauge action with the real action used to
interpret scale-dependent integer temporal translations. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeDiscreteTemporalCompatibility
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (G : E.PhysicalGaugeAction)
    (A : E.PhysicalDiscreteTemporalAction) where
  gauge_commute : ∀ t g X,
    A.physicalTranslate t (G.action g X) =
      G.action g (A.physicalTranslate t X)

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeDiscreteTemporalCompatibility

/-- Dense realizable lattice times, the varying-map weak-limit continuity input,
and gauge commutation construct a genuine continuum real-time symmetry. -/
noncomputable def toContinuumEuclideanTimeTranslation
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {A : E.PhysicalDiscreteTemporalAction}
    (C : E.GaugeDiscreteTemporalCompatibility G A)
    {D : A.DenseTemporalApproximation}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (W : D.WeakLimitContinuity L) :
    PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation
      (G.toSymmetryLimit L) where
  translate := A.physicalTranslate
  translate_zero_apply := A.physicalTranslate_zero_apply
  translate_add_apply := A.physicalTranslate_add_apply
  gauge_commute := C.gauge_commute
  continuumProbabilityMeasure_map_eq_self :=
    W.continuumProbabilityMeasure_map_eq_self

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeDiscreteTemporalCompatibility

end

end MathlibAnalytic
end MGAP4D
