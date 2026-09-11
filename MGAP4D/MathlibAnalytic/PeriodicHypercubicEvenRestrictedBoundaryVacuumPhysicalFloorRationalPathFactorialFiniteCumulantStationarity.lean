import MGAP4D.MathlibAnalytic.FiniteCumulantCombinatorics
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialFiniteNPointStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialCumulantNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialCumulantTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialCumulantCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialCumulantSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialCumulantMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialCumulantBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Untranslated finite rational-time block moment for a time-labelled scalar
observable family.  The observable at a block time `q` is obtained by restricting
the ambient family `O : ℚ → ℝ → ℝ` to the subtype `q : B`. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment
    (μ : Measure (ℚ → ℝ)) (O : ℚ → ℝ → ℝ) (B : Finset ℚ) : ℝ :=
  ∫ y,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointObservableProduct
      B (fun q : B => O q) y ∂
    Measure.map
      (B.restrict (π := fun _ : ℚ => ℝ)) μ

/-- The same finite block moment after a common rational translation of all
its time arguments. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment
    (μ : Measure (ℚ → ℝ)) (O : ℚ → ℝ → ℝ) (B : Finset ℚ) (r : ℚ) : ℝ :=
  ∫ y,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointObservableProduct
      B (fun q : B => O q) y ∂
    Measure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
        B r) μ

/-- Finite rational-time observable cumulant, formed from the untranslated
block moments by the standard finite-partition moment-cumulant formula. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableCumulant
    (μ : Measure (ℚ → ℝ)) (O : ℚ → ℝ → ℝ) (J : Finset ℚ) : ℝ :=
  finiteCumulant J
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment μ O)

/-- Finite rational-time observable cumulant formed from simultaneously
translated block moments. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedCumulant
    (μ : Measure (ℚ → ℝ)) (O : ℚ → ℝ → ℝ) (J : Finset ℚ) (r : ℚ) : ℝ :=
  finiteCumulant J
    (fun B =>
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment
        μ O B r)

/-- Exact common rational-time translation invariance of every finite observable
cumulant of the factorial rational continuum path.

The proof is purely algebraic after the finite n-point theorem: #1685 gives the
translated/untranslated equality for every block moment `B`, and
`finiteCumulant_congr` lifts those equalities through the finite partition sum.
No stochastic continuity, independence, spectral, decay, coercivity, or new
mass-gap assumption is used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableCumulant_shift_eq_self
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
    (J : Finset ℚ) (r : ℚ)
    (O : ℚ → ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedCumulant
        L.continuumMeasure.toMeasure O J r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableCumulant
        L.continuumMeasure.toMeasure O J := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedCumulant
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableCumulant
  apply finiteCumulant_congr J
  intro B
  simpa [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedMoment,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableMoment] using
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableNPointMoment_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L B r
      (fun q : B => O q))

/-- The bare rational coordinate cumulant is the identity-observable
specialization of finite observable cumulant stationarity. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteCoordinateCumulant_shift_eq_self
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
    (J : Finset ℚ) (r : ℚ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableShiftedCumulant
        L.continuumMeasure.toMeasure (fun _ x => x) J r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteObservableCumulant
        L.continuumMeasure.toMeasure (fun _ x => x) J := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableCumulant_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L J r
      (fun _ x => x)

end

end MathlibAnalytic
end MGAP4D
