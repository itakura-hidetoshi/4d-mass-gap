import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalContinuousState

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance restrictedBoundaryVacuumPhysicalObservableAlgebraNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalObservableAlgebraTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalObservableAlgebraCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalObservableAlgebraSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalObservableAlgebraMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalObservableAlgebraBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- On the scalar continuum carrier of the actual restricted boundary-vacuum
readout, the physical gauge-invariant observable algebra is the entire bounded
continuous real observable algebra.

This is stronger than producing one gauge-invariant subtype element at a time:
the already proved identity gauge action makes the fixed-point subalgebra
literally `⊤`.  No time-reflection or additional physical symmetry statement is
used here. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservableSubalgebra_eq_top
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    physicalYangMillsGaugeInvariantObservableSubalgebra
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L) = ⊤ := by
  apply le_antisymm le_top
  intro O _
  exact
    (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L O).property

end

end MathlibAnalytic
end MGAP4D
