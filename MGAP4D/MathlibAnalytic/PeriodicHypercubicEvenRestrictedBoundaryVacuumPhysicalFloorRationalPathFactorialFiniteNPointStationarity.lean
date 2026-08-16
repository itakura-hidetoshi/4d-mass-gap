import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialFiniteJointExpectationStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialNPointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialNPointTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialNPointCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialNPointSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialNPointMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialNPointBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Product of the scalar rational-path coordinates in one finite time set. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCoordinateProduct
    (J : Finset ℚ) (y : ∀ q : J, ℝ) : ℝ :=
  ∏ q : J, y q

/-- Product of a possibly different scalar observable at each rational time. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointObservableProduct
    (J : Finset ℚ) (O : ∀ q : J, ℝ → ℝ) (y : ∀ q : J, ℝ) : ℝ :=
  ∏ q : J, O q (y q)

/-- Centered product associated with arbitrary prescribed one-point centers.
This is the raw centered-moment surface used downstream before any cumulant or
connected-correlation combinatorics is imposed. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCenteredObservableProduct
    (J : Finset ℚ) (O : ∀ q : J, ℝ → ℝ) (center : ∀ q : J, ℝ)
    (y : ∀ q : J, ℝ) : ℝ :=
  ∏ q : J, (O q (y q) - center q)

/-- The bare scalar rational path has exact finite n-point moment invariance
under a common rational translation of every time argument.  This is a direct
specialization of finite-joint-law stationarity and therefore does not infer a
joint statement from one-time marginals. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteNPointMoment_shift_eq_self
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
    (∫ y,
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCoordinateProduct
          J y ∂
        Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
            J r)
          L.continuumMeasure.toMeasure) =
      ∫ y,
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCoordinateProduct
          J y ∂
        Measure.map
          (J.restrict (π := fun _ : ℚ => ℝ))
          L.continuumMeasure.toMeasure := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteJointIntegral_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L J r
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCoordinateProduct J)

/-- Exact common-time-translation invariance for a finite product of arbitrary
scalar observables attached to the rational times in `J`.

This is the OS/Wightman-facing finite n-point surface: any required
measurability or integrability estimates belong to the chosen observables, not
to the stationarity argument. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteObservableNPointMoment_shift_eq_self
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
    (O : ∀ q : J, ℝ → ℝ) :
    (∫ y,
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointObservableProduct
          J O y ∂
        Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
            J r)
          L.continuumMeasure.toMeasure) =
      ∫ y,
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointObservableProduct
          J O y ∂
        Measure.map
          (J.restrict (π := fun _ : ℚ => ℝ))
          L.continuumMeasure.toMeasure := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteJointIntegral_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L J r
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointObservableProduct
        J O)

/-- The same common rational translation leaves every finite centered product
unchanged in expectation for arbitrary fixed centers.  In particular, once the
centers are chosen to be the one-point expectations, this is the centered
n-point input needed for connected-correlation/cumulant constructions. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteCenteredNPointMoment_shift_eq_self
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
    (O : ∀ q : J, ℝ → ℝ) (center : ∀ q : J, ℝ) :
    (∫ y,
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCenteredObservableProduct
          J O center y ∂
        Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
            J r)
          L.continuumMeasure.toMeasure) =
      ∫ y,
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCenteredObservableProduct
          J O center y ∂
        Measure.map
          (J.restrict (π := fun _ : ℚ => ℝ))
          L.continuumMeasure.toMeasure := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteJointIntegral_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L J r
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointCenteredObservableProduct
        J O center)

end

end MathlibAnalytic
end MGAP4D
