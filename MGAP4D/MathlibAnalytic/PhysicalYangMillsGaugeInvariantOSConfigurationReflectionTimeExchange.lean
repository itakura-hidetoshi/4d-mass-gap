import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Configuration-space realization of Euclidean time translation and reflection.

The abstract OS reflection is identified with precomposition by a configuration
homeomorphism.  The configuration identity

`tau_t (theta A) = theta (tau_t⁻¹ A)`

then generates the observable identity

`Theta (alpha_t O) = alpha_t⁻¹ (Theta O)`.
-/
structure ConfigurationReflectionTimeExchange
    (T : P.PositiveTimeObservableContractionSemigroup) where
  configurationTranslate : NNReal →
    Homeomorph S.Configuration S.Configuration
  gauge_commute : ∀ t g A,
    configurationTranslate t (S.action g A) =
      S.action g (configurationTranslate t A)
  configurationReflection :
    Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g A,
    configurationReflection (S.action g A) =
      S.action g (configurationReflection A)
  reflection_realization : ∀ O,
    D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O
  reflection_time_exchange : ∀ t A,
    configurationTranslate t (configurationReflection A) =
      configurationReflection ((configurationTranslate t).symm A)
  positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
    physicalGaugeInvariantObservablePrecompAlgEquiv S
        (configurationTranslate t) (gauge_commute t)
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      (T.translate t F :
        physicalYangMillsGaugeInvariantObservableSubalgebra S)
  continuumMeasure_invariant : ∀ t,
    Measure.map (configurationTranslate t)
        (S.continuumMeasure : Measure S.Configuration) =
      (S.continuumMeasure : Measure S.Configuration)
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S

namespace ConfigurationReflectionTimeExchange

/-- Configuration reflection and time-translation exchange imply the corresponding
covariance identity on the full gauge-invariant observable algebra. -/
theorem observable_reflection_translate
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.ConfigurationReflectionTimeExchange)
    (t : NNReal)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    D.reflection
        (physicalGaugeInvariantObservablePrecompAlgEquiv S
          (G.configurationTranslate t) (G.gauge_commute t) O) =
      (physicalGaugeInvariantObservablePrecompAlgEquiv S
        (G.configurationTranslate t) (G.gauge_commute t)).symm
          (D.reflection O) := by
  rw [G.reflection_realization, G.reflection_realization]
  apply Subtype.ext
  ext A
  change
    (O : BoundedContinuousFunction S.Configuration ℝ)
        (G.configurationTranslate t (G.configurationReflection A)) =
      (O : BoundedContinuousFunction S.Configuration ℝ)
        (G.configurationReflection ((G.configurationTranslate t).symm A))
  rw [G.reflection_time_exchange]

/-- Configuration reflection geometry generates the configuration time-translation
covariance package used by the Hamiltonian self-adjointness theorem. -/
theorem toConfigurationTimeTranslationCovariance
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.ConfigurationReflectionTimeExchange) :
    T.ConfigurationTimeTranslationCovariance where
  configurationTranslate := G.configurationTranslate
  gauge_commute := G.gauge_commute
  positive_restriction := G.positive_restriction
  reflection_translate := G.observable_reflection_translate
  continuumMeasure_invariant := G.continuumMeasure_invariant
  omega_eq_continuumState := G.omega_eq_continuumState

/-- Configuration-level reflection/time geometry and observable-state strong
continuity imply self-adjointness of the graph-closed physical Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.ConfigurationReflectionTimeExchange)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian :=
  G.toConfigurationTimeTranslationCovariance.closedRightHamiltonian_isSelfAdjoint
    hContinuous

end ConfigurationReflectionTimeExchange

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
