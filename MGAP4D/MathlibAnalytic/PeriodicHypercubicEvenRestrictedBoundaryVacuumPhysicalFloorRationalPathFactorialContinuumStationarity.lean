import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExactLatticeShift
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEventualStationarityLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialStationarityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialStationarityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialStationarityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialStationaritySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialStationarityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- For the canonical factorial lattice spacing `a_n = (n!)⁻¹`, every fixed
rational translation acts exactly stationarily on the continuum rational path
law extracted along any Prokhorov subsequence.

For a fixed `r : ℚ`, factorial divisibility makes `r` an exact lattice-time
multiple at all sufficiently large scales.  Cofinality of the strict Prokhorov
subsequence preserves that eventual exact alignment.  The finite-scale full
path law is therefore eventually exactly invariant, and weak-limit uniqueness
passes this stationarity to the continuum law.

No multi-time stochastic-continuity or independence premise is used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_shift_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (r : ℚ) :
    L.continuumMeasure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable =
      L.continuumMeasure := by
  apply
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_shift_eq_of_eventually_embeddedMeasure_map_shift_eq_self
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L r
  have hAligned :
      ∀ᶠ n : ℕ in atTop,
        ∃ k : ℤ,
          (r : ℝ) =
            (k : ℝ) *
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence n) := by
    exact
      L.subsequence_strictMono.tendsto_atTop.eventually
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_eventually_latticeMultiple
          r)
  filter_upwards [hAligned] with n hn
  rcases hn with ⟨k, hk⟩
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_map_exactLatticeShift_eq_self
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      (L.subsequence n) r k hk

/-- Universal rational-time stationarity of the factorial-spacing continuum path
law.  This is the full countable rational translation action, not merely a
one-coordinate marginal statement. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_stationary
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    ∀ r : ℚ,
      L.continuumMeasure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable =
        L.continuumMeasure := by
  intro r
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L r

end

end MathlibAnalytic
end MGAP4D
