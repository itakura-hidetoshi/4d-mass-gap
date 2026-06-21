import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedHaarFactorization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The exact Wilson Gibbs density in the canonical boundary/open-half/open-half
coordinates of the even periodic `SU(N)` lattice. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ≥0∞ := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  exact C.boundaryFiberedGibbsDensity
    (periodicHypercubicEvenEdgeOrbitPartition H)

/-- The concrete boundary-fibered periodic `SU(N)` Gibbs density is measurable. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity, C] using
    C.boundaryFiberedGibbsDensity_measurable
      (periodicHypercubicEvenEdgeOrbitPartition H)

/-- Exact boundary-fibered pushforward of the actual finite-volume even-periodic
`SU(N)` Wilson Gibbs law.

The reference law contains one copy of every reflection-fixed physical link and
two identical open-half Haar products.  Every interaction, including crossing
plaquettes, remains in the explicit pulled-back Gibbs density. -/
theorem periodicHypercubicEvenSpecialUnitary_map_boundaryFiberedCoordinates_gibbsMeasure
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure.map
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedCoordinates
          (Matrix.specialUnitaryGroup (Fin N) ℂ))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      (((periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure
          (normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
        (((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
            (normalizedCompactHaar
              (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
          ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
            (normalizedCompactHaar
              (Matrix.specialUnitaryGroup (Fin N) ℂ))))).withDensity
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  simpa [periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity, C] using
    C.map_boundaryFiberedCoordinates_gibbsMeasure
      (periodicHypercubicEvenEdgeOrbitPartition H)

end

end MathlibAnalytic
end MGAP4D
