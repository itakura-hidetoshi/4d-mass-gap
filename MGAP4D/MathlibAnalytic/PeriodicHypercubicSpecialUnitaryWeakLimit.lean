import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNormalizedAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonActionPointwiseBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProperCoerciveFunctional

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Exact signed periodic `SU(N)` Wilson laws, reciprocal plaquette-volume
normalization, and one proper physical functional controlled by the normalized
action produce a physical continuum weak limit.

All finite-volume probability normalization, gauge invariance, the universal
action bound `≤ 2`, moment control, compact containment, tightness, and
Prokhorov extraction are generated internally. -/
noncomputable def
    periodicHypercubicSpecialUnitaryWeakLimitOfProperNNRealFunctional
    {PhysicalConfiguration : Type}
    [TopologicalSpace PhysicalConfiguration]
    [MeasurableSpace PhysicalConfiguration]
    [BorelSpace PhysicalConfiguration]
    [PolishSpace PhysicalConfiguration]
    (sideLength : ℕ → ℕ)
    (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n)
    (interpolate :
      ∀ n,
        (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
          (sideLength n) N (sideLength_pos n) hN
          (beta n) (beta_nonneg n)).base.Configuration →
          PhysicalConfiguration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (functional : PhysicalConfiguration → NNReal)
    (functional_proper : IsProperMap functional)
    (functional_le_action :
      ∀ n
        (U :
          (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
            (sideLength n) N (sideLength_pos n) hN
            (beta n) (beta_nonneg n)).base.Configuration),
        (functional (interpolate n U) : ENNReal) ≤
          periodicHypercubicOrientedReciprocalPlaquetteScale (sideLength n) *
            ENNReal.ofReal
              ((periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
                (sideLength n) N (sideLength_pos n) hN
                (beta n) (beta_nonneg n)).base.wilsonAction U)) :
    PhysicalFourDimensionalYangMillsWeakLimit := by
  let E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding :=
    periodicHypercubicSpecialUnitaryPhysicalEmbedding
      sideLength sideLength_pos N hN beta beta_nonneg
      interpolate interpolate_measurable
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop
  let scale : ℕ → ENNReal := fun n =>
    periodicHypercubicOrientedReciprocalPlaquetteScale (sideLength n)
  let offset : ℕ → ENNReal := fun _ => 0
  let Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional :=
    NaturalRadiusCoerciveFunctional.ofProperNNReal
      functional functional_proper
  let B : E.WilsonActionControlUniformPointwiseBound scale offset :=
    { bound := 2
      bound_ne_top := by simp
      pointwise_le := by
        intro n U
        change
          periodicHypercubicOrientedReciprocalPlaquetteScale (sideLength n) *
                ENNReal.ofReal
                  ((periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
                    (sideLength n) N (sideLength_pos n) hN
                    (beta n) (beta_nonneg n)).base.wilsonAction U) +
              0 ≤
            2
        simpa using
          periodicHypercubicSpecialUnitaryReciprocalActionObservable_le_two
            (sideLength n) N (sideLength_pos n) hN
            (beta n) (beta_nonneg n) U }
  let D : E.WilsonActionControlsFunctional Phi scale offset :=
    { pointwise_le := by
        intro n U
        change
          (functional (interpolate n U) : ENNReal) ≤
            periodicHypercubicOrientedReciprocalPlaquetteScale (sideLength n) *
                ENNReal.ofReal
                  ((periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
                    (sideLength n) N (sideLength_pos n) hN
                    (beta n) (beta_nonneg n)).base.wilsonAction U) +
              0
        simpa using functional_le_action n U }
  exact B.toWeakLimit D

end

end MathlibAnalytic
end MGAP4D
