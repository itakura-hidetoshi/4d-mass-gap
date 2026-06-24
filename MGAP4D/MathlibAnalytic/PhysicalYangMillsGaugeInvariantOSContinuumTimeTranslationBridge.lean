import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumEuclideanTimeTranslation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
namespace PositiveTimeObservableContractionSemigroup
namespace ConfigurationTimeTranslationCovariance

/-- Feed a continuum-only Euclidean-time action into the OS configuration-time
covariance interface.

The continuum measure invariance field is generated from the dense lattice-time
weak-limit bridge.  The remaining inputs are exactly the observable restriction,
reflection exchange, and state identification data. -/
noncomputable def ofContinuumEuclideanTimeTranslation
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
      physicalGaugeInvariantObservablePrecompAlgEquiv S
          (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ))
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
        (T.translate t F : physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (reflection_translate : ∀ (t : NNReal)
      (O : physicalYangMillsGaugeInvariantObservableSubalgebra S),
      D.reflection
          (physicalGaugeInvariantObservablePrecompAlgEquiv S
            (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ)) O) =
        (physicalGaugeInvariantObservablePrecompAlgEquiv S
          (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ))).symm
            (D.reflection O))
    (omega_eq_continuumState :
      P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S) :
    T.ConfigurationTimeTranslationCovariance where
  configurationTranslate t := E.translate (t : ℝ)
  gauge_commute t := E.gauge_commute (t : ℝ)
  positive_restriction := positive_restriction
  reflection_translate := reflection_translate
  continuumMeasure_invariant t := E.continuumMeasure_map_eq_self (t : ℝ)
  omega_eq_continuumState := omega_eq_continuumState

end ConfigurationTimeTranslationCovariance
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
