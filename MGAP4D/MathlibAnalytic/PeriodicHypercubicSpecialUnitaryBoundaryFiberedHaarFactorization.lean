import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonBoundaryFiberedHaarFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

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

/-- Concrete boundary-fibered factorization of the product normalized Haar law
for the canonical even-periodic `SU(N)` Wilson system. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedHaarFactorization
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryFiberedMeasureFactorization
      (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let L := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  exact L.base.boundaryFiberedHaarMeasureFactorization
    (periodicHypercubicEvenEdgeOrbitPartition H)

@[simp]
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedHaarFactorization_fullMeasure
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedHaarFactorization
        H N hN beta hbeta).fullMeasure =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure := by
  rfl

/-- The physical product Haar law pushes forward exactly to one shared boundary
Haar product and two identical open-half Haar products. -/
theorem periodicHypercubicEvenSpecialUnitary_map_boundaryFiberedCoordinates_configurationHaarMeasure
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure.map
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedCoordinates
          (Matrix.specialUnitaryGroup (Fin N) ℂ))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure =
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure
          (normalizedCompactHaar
            (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
        (((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
            (normalizedCompactHaar
              (Matrix.specialUnitaryGroup (Fin N) ℂ))).prod
          ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
            (normalizedCompactHaar
              (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  let L := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  simpa [L] using
    L.base.map_boundaryFiberedCoordinates_configurationHaarMeasure
      (periodicHypercubicEvenEdgeOrbitPartition H)

end

end MathlibAnalytic
end MGAP4D
