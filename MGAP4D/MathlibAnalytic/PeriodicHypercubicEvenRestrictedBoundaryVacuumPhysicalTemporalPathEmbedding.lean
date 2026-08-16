import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalPathLaw
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumTemporalPathEmbeddingNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalPathEmbeddingTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalPathEmbeddingCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalPathEmbeddingSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalPathEmbeddingMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalPathEmbeddingBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The entire integer-time boundary-vacuum history, rather than one scalar
slice, as the fixed physical Polish carrier for the actual finite Wilson
systems.

At every lattice scale the interpolation is the concrete stationary temporal
path readout constructed from the same Wilson configuration.  This keeps time
translation nontrivial while placing all lattice scales in one common carrier
`ℤ → ℝ`. -/
@[reducible] noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop) :
    ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding where
  PhysicalConfiguration := ℤ → ℝ
  system := fun n =>
    periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (H n)) N hN
      (beta n) (hbeta n)
  interpolate := fun n A =>
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
      (H n) N hN (beta n) (hbeta n) A
  interpolate_measurable := fun n =>
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
      (H n) N hN (beta n) (hbeta n)
  latticeSpacing := latticeSpacing
  latticeSpacing_pos := latticeSpacing_pos
  latticeSpacing_tendsto_zero := latticeSpacing_tendsto_zero
  physicalVolume := physicalVolume
  physicalVolume_tendsto_atTop := physicalVolume_tendsto_atTop

/-- The generic embedded probability law of the path-valued physical embedding
is definitionally the stationary temporal path probability measure constructed
from the same finite Wilson Gibbs law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure n =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure
        (H n) N hN (beta n) (hbeta n) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
