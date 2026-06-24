import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDiscretePhysicalTemporalAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedFloorTemporalApproximation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical floor-based dense temporal approximation attached to the
periodic `SU(N)` discrete physical temporal action.

The integer step at scale `n` is `⌊t / aₙ⌋`; its realized physical time is
`aₙ * ⌊t / aₙ⌋`, which converges to `t` because `aₙ > 0` and `aₙ → 0`. -/
noncomputable def periodicHypercubicSpecialUnitaryFloorDenseTemporalApproximation
    {PhysicalConfiguration : Type}
    [TopologicalSpace PhysicalConfiguration] [MeasurableSpace PhysicalConfiguration]
    [BorelSpace PhysicalConfiguration] [PolishSpace PhysicalConfiguration]
    (sideLength : ℕ → ℕ) (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ) (hN : 0 < N) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (beta_nonneg : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n,
      (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide (sideLength n) N
        (sideLength_pos n) hN (beta n) (beta_nonneg n)).base.Configuration →
        PhysicalConfiguration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (latticeSpacing : ℕ → ℝ) (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (physicalTranslate : ℝ → Homeomorph PhysicalConfiguration PhysicalConfiguration)
    (physicalTranslate_zero_apply : ∀ A, physicalTranslate 0 A = A)
    (physicalTranslate_add_apply : ∀ s t A,
      physicalTranslate (s + t) A = physicalTranslate s (physicalTranslate t A))
    (interpolate_integerTemporal_equivariant : ∀ n k U,
      interpolate n
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (sideLength n) k U) =
        physicalTranslate ((k : ℝ) * latticeSpacing n) (interpolate n U)) :
    (periodicHypercubicSpecialUnitaryDiscretePhysicalTemporalAction
      sideLength sideLength_pos N hN beta beta_nonneg
      interpolate interpolate_measurable latticeSpacing latticeSpacing_pos
      latticeSpacing_tendsto_zero physicalVolume physicalVolume_tendsto_atTop
      physicalTranslate physicalTranslate_zero_apply physicalTranslate_add_apply
      interpolate_integerTemporal_equivariant).DenseTemporalApproximation :=
  ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction.DenseTemporalApproximation.ofFloor
    (A := periodicHypercubicSpecialUnitaryDiscretePhysicalTemporalAction
      sideLength sideLength_pos N hN beta beta_nonneg
      interpolate interpolate_measurable latticeSpacing latticeSpacing_pos
      latticeSpacing_tendsto_zero physicalVolume physicalVolume_tendsto_atTop
      physicalTranslate physicalTranslate_zero_apply physicalTranslate_add_apply
      interpolate_integerTemporal_equivariant)
    (fun _ _ => rfl)

end

end MathlibAnalytic
end MGAP4D
