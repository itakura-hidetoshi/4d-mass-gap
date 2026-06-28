import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumTimeTranslationFromDiscrete
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumTimeTranslationBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
namespace PositiveTimeObservableContractionSemigroup
namespace ConfigurationTimeTranslationCovariance

/-- The three OS-specific compatibility inputs that remain after a continuum
Euclidean-time action and its invariant continuum law have been constructed. -/
structure ContinuumCompatibility
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    (T : P.PositiveTimeObservableContractionSemigroup)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S) : Prop where
  positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
    physicalGaugeInvariantObservablePrecompAlgEquiv S
        (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ))
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      (T.translate t F : physicalYangMillsGaugeInvariantObservableSubalgebra S)
  reflection_translate : ∀ (t : NNReal)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S),
    D.reflection
        (physicalGaugeInvariantObservablePrecompAlgEquiv S
          (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ)) O) =
      (physicalGaugeInvariantObservablePrecompAlgEquiv S
        (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ))).symm
          (D.reflection O)
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S

namespace ContinuumCompatibility

/-- Package the remaining OS-specific compatibility data into the existing
configuration-time covariance interface. -/
noncomputable def toConfigurationTimeTranslationCovariance
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    (H : ContinuumCompatibility T E) :
    T.ConfigurationTimeTranslationCovariance :=
  ConfigurationTimeTranslationCovariance.ofContinuumEuclideanTimeTranslation E
    H.positive_restriction H.reflection_translate H.omega_eq_continuumState

end ContinuumCompatibility

/-- Complete the configuration-time covariance bridge directly from the exact
finite integer action.

The floor selector supplies dense realizable times, joint continuity transports
the weak limit through those varying times, and the final compatibility record
contains only the positive-time observable restriction, reflection exchange,
and continuum-state identification. -/
noncomputable def ofDiscreteTemporalAction
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction}
    {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E₀.latticeSpacing n)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : ContinuumCompatibility T
      (C.toContinuumEuclideanTimeTranslationOfFloor J latticeTime_eq L)) :
    T.ConfigurationTimeTranslationCovariance :=
  H.toConfigurationTimeTranslationCovariance

end ConfigurationTimeTranslationCovariance
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
