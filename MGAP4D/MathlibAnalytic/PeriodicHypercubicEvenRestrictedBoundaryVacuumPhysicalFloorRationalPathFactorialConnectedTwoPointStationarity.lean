import MGAP4D.MathlibAnalytic.TwoPointConnectedCorrelationAlgebra
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialFiniteCumulantStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedTwoPointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedTwoPointTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedTwoPointCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedTwoPointSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedTwoPointMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedTwoPointBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The finite observable block moment itself is invariant under a common
rational translation.  This packages the #1685 n-point theorem in the block-
moment notation used by the cumulant and connected-correlation APIs. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableShiftedMoment_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (B : Finset ℚ) (r : ℚ)
    (O : ℚ → ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment
        L.continuumMeasure.toMeasure O B r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment
        L.continuumMeasure.toMeasure O B := by
  simpa [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment] using
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableNPointMoment_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L B r
      (fun q : B => O q))

/-- The rational-time two-point connected expression
`M_{q₁,q₂} - M_{q₁} M_{q₂}` for a time-labelled scalar observable family.
For distinct `q₁` and `q₂` this is the standard connected two-point correlation
(second cumulant) attached to those two rational times. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalObservableTwoPointConnectedCorrelation
    (μ : Measure (ℚ → ℝ)) (O : ℚ → ℝ → ℝ) (q₁ q₂ : ℚ) : ℝ :=
  twoPointConnectedCorrelation
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment
      μ O {q₁, q₂})
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment
      μ O {q₁})
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment
      μ O {q₂})

/-- The same two-point connected expression after translating both rational
time arguments by the same `r`. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalObservableShiftedTwoPointConnectedCorrelation
    (μ : Measure (ℚ → ℝ)) (O : ℚ → ℝ → ℝ) (q₁ q₂ r : ℚ) : ℝ :=
  twoPointConnectedCorrelation
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment
      μ O {q₁, q₂} r)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment
      μ O {q₁} r)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment
      μ O {q₂} r)

/-- Exact common rational-time translation invariance of the connected two-point
correlation surface.  The proof uses only the already established exact block-
moment stationarity and the algebraic second-cumulant formula; it introduces no
new stochastic continuity, independence, spectral, decay, coercivity, or
mass-gap assumption. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_observableTwoPointConnectedCorrelation_shift_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (q₁ q₂ r : ℚ)
    (O : ℚ → ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalObservableShiftedTwoPointConnectedCorrelation
        L.continuumMeasure.toMeasure O q₁ q₂ r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalObservableTwoPointConnectedCorrelation
        L.continuumMeasure.toMeasure O q₁ q₂ := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalObservableShiftedTwoPointConnectedCorrelation
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalObservableTwoPointConnectedCorrelation
  apply twoPointConnectedCorrelation_congr
  · exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableShiftedMoment_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L {q₁, q₂} r O
  · exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableShiftedMoment_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L {q₁} r O
  · exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableShiftedMoment_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L {q₂} r O

end

end MathlibAnalytic
end MGAP4D
