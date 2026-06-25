import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumTimeTranslationFromDiscrete
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationReflectionTimeExchange

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Reflection compatibility for the continuum-only Euclidean-time action.

This interface is the continuum-time counterpart of
`WeakLimitTimeReflectionBridge`.  It does not require every finite
approximating law to be invariant under the exact target real time.  Hence it
can be instantiated by the dense lattice-time and joint-continuity route. -/
structure ContinuumTimeReflectionBridge
    (T : P.PositiveTimeObservableContractionSemigroup)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S) where
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g X,
    configurationReflection (S.action g X) =
      S.action g (configurationReflection X)
  reflection_realization : ∀ O,
    D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O
  reflection_translate_neg : ∀ t X,
    configurationReflection (E.translate t X) =
      E.translate (-t) (configurationReflection X)
  positive_restriction : ∀ (t : NNReal) (F : D.positiveTimeSubalgebra),
    physicalGaugeInvariantObservablePrecompAlgEquiv S
        (E.translate (t : ℝ)) (E.gauge_commute (t : ℝ))
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) =
      (T.translate t F :
        physicalYangMillsGaugeInvariantObservableSubalgebra S)
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S

namespace ContinuumTimeReflectionBridge

variable {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- Reflection converts positive continuum time translation into the inverse
translation. -/
theorem reflection_time_exchange
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.ContinuumTimeReflectionBridge E)
    (t : NNReal) (X : S.Configuration) :
    E.translate (t : ℝ) (G.configurationReflection X) =
      G.configurationReflection ((E.translate (t : ℝ)).symm X) := by
  calc
    E.translate (t : ℝ) (G.configurationReflection X) =
        G.configurationReflection (E.translate (-(t : ℝ)) X) := by
      simpa using (G.reflection_translate_neg (-(t : ℝ)) X).symm
    _ = G.configurationReflection ((E.translate (t : ℝ)).symm X) := by
      rw [E.translate_symm_apply_eq_neg]

/-- The continuum-only reflection bridge supplies the existing configuration
reflection/time-exchange interface. -/
noncomputable def toConfigurationReflectionTimeExchange
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.ContinuumTimeReflectionBridge E) :
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

/-- The continuum-only reflection bridge closes the conditional
self-adjointness route for the graph-closed OS Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint
    {T : P.PositiveTimeObservableContractionSemigroup}
    (G : T.ContinuumTimeReflectionBridge E)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian :=
  G.toConfigurationReflectionTimeExchange.closedRightHamiltonian_isSelfAdjoint
    hContinuous

/-- The geometric and OS compatibility data remaining after exact finite
integer temporal translations have been promoted to a continuum real-time
action by floor approximation and joint continuity. -/
structure DiscreteFloorCompatibility
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction}
    {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D₀ : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    {P₀ : D₀.OSPreHilbertData}
    (T : P₀.PositiveTimeObservableContractionSemigroup) where
  configurationReflection : Homeomorph
    (G.toSymmetryLimit L).Configuration
    (G.toSymmetryLimit L).Configuration
  reflection_gauge_commute : ∀ g X,
    configurationReflection ((G.toSymmetryLimit L).action g X) =
      (G.toSymmetryLimit L).action g (configurationReflection X)
  reflection_realization : ∀ O,
    D₀.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv (G.toSymmetryLimit L)
        configurationReflection reflection_gauge_commute O
  reflection_translate_neg : ∀ t X,
    configurationReflection (A.physicalTranslate t X) =
      A.physicalTranslate (-t) (configurationReflection X)
  positive_restriction : ∀ (t : NNReal) (F : D₀.positiveTimeSubalgebra),
    physicalGaugeInvariantObservablePrecompAlgEquiv (G.toSymmetryLimit L)
        (A.physicalTranslate (t : ℝ)) (C.gauge_commute (t : ℝ))
        (F : physicalYangMillsGaugeInvariantObservableSubalgebra
          (G.toSymmetryLimit L)) =
      (T.translate t F : physicalYangMillsGaugeInvariantObservableSubalgebra
        (G.toSymmetryLimit L))
  omega_eq_continuumState :
    P₀.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState
      (G.toSymmetryLimit L)

/-- Construct the continuum-only reflection bridge directly from the exact
finite integer temporal action, the floor dense-time selector, and joint
continuity. -/
noncomputable def ofDiscreteTemporalActionOfFloor
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A) (J : A.JointContinuity)
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E₀.latticeSpacing n)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D₀ : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P₀ : D₀.OSPreHilbertData}
    {T : P₀.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T) :
    T.ContinuumTimeReflectionBridge
      (C.toContinuumEuclideanTimeTranslationOfFloor J latticeTime_eq L) where
  configurationReflection := H.configurationReflection
  reflection_gauge_commute := H.reflection_gauge_commute
  reflection_realization := H.reflection_realization
  reflection_translate_neg := H.reflection_translate_neg
  positive_restriction := H.positive_restriction
  omega_eq_continuumState := H.omega_eq_continuumState

end ContinuumTimeReflectionBridge

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
