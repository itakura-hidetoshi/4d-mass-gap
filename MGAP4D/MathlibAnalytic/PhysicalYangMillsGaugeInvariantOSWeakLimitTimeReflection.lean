import MGAP4D.MathlibAnalytic.PhysicalYangMillsEuclideanTimeTranslationLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationReflectionTimeExchange

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

structure WeakLimitTimeReflectionBridge
    (T : P.PositiveTimeObservableContractionSemigroup)
    (E : PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit S) where
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g A,
    configurationReflection (S.action g A) =
      S.action g (configurationReflection A)
  reflection_realization : ∀ O,
    D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O
  reflection_translate_neg : ∀ t A,
    configurationReflection (E.translate t A) =
      E.translate (-t) (configurationReflection A)
  positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
    physicalGaugeInvariantObservablePrecompAlgEquiv S
        (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ))
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      (T.translate t F : physicalYangMillsGaugeInvariantObservableSubalgebra S)
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S

namespace WeakLimitTimeReflectionBridge

variable {E : PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit S}

theorem reflection_time_exchange
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.WeakLimitTimeReflectionBridge E)
    (t : NNReal) (A : S.Configuration) :
    E.translate (t : ℝ) (G.configurationReflection A) =
      G.configurationReflection ((E.translate (t : ℝ)).symm A) := by
  calc
    E.translate (t : ℝ) (G.configurationReflection A) =
        G.configurationReflection (E.translate (-(t : ℝ)) A) := by
      simpa using (G.reflection_translate_neg (-(t : ℝ)) A).symm
    _ = G.configurationReflection ((E.translate (t : ℝ)).symm A) := by
      rw [E.translate_symm_apply_eq_neg]

noncomputable def toConfigurationReflectionTimeExchange
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.WeakLimitTimeReflectionBridge E) :
    T.ConfigurationReflectionTimeExchange where
  configurationTranslate t := E.translate (t : ℝ)
  gauge_commute t := E.gauge_commute (t : ℝ)
  configurationReflection := G.configurationReflection
  reflection_gauge_commute := G.reflection_gauge_commute
  reflection_realization := G.reflection_realization
  reflection_time_exchange := G.reflection_time_exchange
  positive_restriction := G.positive_restriction
  continuumMeasure_invariant t := E.continuumMeasure_map_eq_self (t : ℝ)
  omega_eq_continuumState := G.omega_eq_continuumState

theorem closedRightHamiltonian_isSelfAdjoint
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.WeakLimitTimeReflectionBridge E)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian :=
  G.toConfigurationReflectionTimeExchange.closedRightHamiltonian_isSelfAdjoint
    hContinuous

end WeakLimitTimeReflectionBridge

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
