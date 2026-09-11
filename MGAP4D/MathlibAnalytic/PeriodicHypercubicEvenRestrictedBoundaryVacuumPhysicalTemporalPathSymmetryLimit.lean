import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalPathEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumTemporalPathSymmetryNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalPathSymmetryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalPathSymmetryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalPathSymmetrySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalPathSymmetryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalPathSymmetryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Integer translation of the scalar path is continuous for the product
Polish topology on `ℤ → ℝ`. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_continuous
    (k : ℤ) :
    Continuous
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k) := by
  exact continuous_pi (fun t => continuous_apply (t + k))

/-- The generic embedded path probability law is exactly invariant under every
integer path shift.

This is a `ProbabilityMeasure`-level repackaging of the already proved finite
Wilson path stationarity. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_map_shift_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (n : ℕ) (k : ℤ) :
    let E :=
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
    (E.embeddedMeasure n).map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_continuous k).measurable.aemeasurable =
      E.embeddedMeasure n := by
  dsimp only
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_eq]
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  simp only [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_toMeasure]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_map_shift_eq_self
      (H n) N hN (beta n) (hbeta n) k

/-- Any Prokhorov subsequential limit of the stationary finite Wilson path laws
inherits the integer path shifts as an actual continuous physical symmetry.

No additional stationarity or continuum symmetry hypothesis is supplied. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathSymmetryLimit
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    PhysicalFourDimensionalYangMillsSymmetryLimit :=
  { L.toWeakLimit with
    Symmetry := ℤ
    action := periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
    action_continuous :=
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_continuous
    approximatingInvariant := fun n k =>
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_map_shift_eq_self
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop
        (L.subsequence n) k }

/-- Integer path-shift stationarity therefore survives exactly in the continuum
weak limit. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_continuumMeasure_map_shift_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (k : ℤ) :
    let S :=
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L
    S.continuumMeasure.map
        (S.action_continuous k).measurable.aemeasurable =
      S.continuumMeasure := by
  dsimp only
  exact
    physical_yang_mills_symmetry_passes_to_weak_limit
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L) k

end

end MathlibAnalytic
end MGAP4D
