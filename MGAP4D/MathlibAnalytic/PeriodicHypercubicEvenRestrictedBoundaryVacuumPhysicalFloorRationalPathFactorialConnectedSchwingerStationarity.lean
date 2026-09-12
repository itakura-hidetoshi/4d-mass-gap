import MGAP4D.MathlibAnalytic.FiniteConnectedCorrelationCombinatorics
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialFiniteSlotStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialConnectedSchwingerBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Product of the observables attached to a finite block of labelled slots. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableProduct
    {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (O : ι → ℝ → ℝ) (y : ι → ℝ) : ℝ :=
  ∏ i ∈ B, O i (y i)

/-- Untranslated block moment of labelled rational-time observables. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableMoment
    {ι : Type*} [DecidableEq ι]
    (μ : Measure (ℚ → ℝ)) (time : ι → ℚ) (O : ι → ℝ → ℝ)
    (B : Finset ι) : ℝ :=
  ∫ y,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableProduct
      B O y ∂
    Measure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time)
      μ

/-- Block moment after one common rational translation of every slot time. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableShiftedMoment
    {ι : Type*} [DecidableEq ι]
    (μ : Measure (ℚ → ℝ)) (time : ι → ℚ) (O : ι → ℝ → ℝ)
    (B : Finset ι) (r : ℚ) : ℝ :=
  ∫ y,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableProduct
      B O y ∂
    Measure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
        time r)
      μ

/-- Every labelled finite block moment is exactly invariant under a common
rational translation. No injectivity of `time` is required. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotObservableMoment_shift_eq_self
    {ι : Type*} [DecidableEq ι]
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
    (time : ι → ℚ) (r : ℚ) (O : ι → ℝ → ℝ) (B : Finset ι) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableShiftedMoment
        L.continuumMeasure.toMeasure time O B r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableMoment
        L.continuumMeasure.toMeasure time O B := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotIntegral_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableProduct
        B O)

/-- Connected finite correlation of a labelled slot family, defined by the full
finite-partition cumulant of its block moments. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotConnectedCorrelation
    {ι : Type*} [DecidableEq ι]
    (μ : Measure (ℚ → ℝ)) (time : ι → ℚ) (O : ι → ℝ → ℝ)
    (J : Finset ι) : ℝ :=
  finiteConnectedCorrelation J
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableMoment
      μ time O)

/-- Connected finite correlation formed from the commonly translated block
moments. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftedConnectedCorrelation
    {ι : Type*} [DecidableEq ι]
    (μ : Measure (ℚ → ℝ)) (time : ι → ℚ) (O : ι → ℝ → ℝ)
    (J : Finset ι) (r : ℚ) : ℝ :=
  finiteConnectedCorrelation J
    (fun B =>
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableShiftedMoment
        μ time O B r)

/-- Exact common rational-time translation invariance of every finite connected
correlation of labelled slots. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotConnectedCorrelation_shift_eq_self
    {ι : Type*} [DecidableEq ι]
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
    (time : ι → ℚ) (r : ℚ) (O : ι → ℝ → ℝ) (J : Finset ι) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftedConnectedCorrelation
        L.continuumMeasure.toMeasure time O J r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotConnectedCorrelation
        L.continuumMeasure.toMeasure time O J := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftedConnectedCorrelation
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotConnectedCorrelation
  apply finiteConnectedCorrelation_congr J
  intro B
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotObservableMoment_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r O B

/-- Explicit connected two-point function of two labelled slots.

This extends the existing rational-time-value two-point API to labelled slots:
the slots remain distinct even when `time 0 = time 1`, so different observables
may be inserted at one rational time without collapsing the correlator. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalSlotTwoPointConnectedCorrelation
    (μ : Measure (ℚ → ℝ)) (time : Fin 2 → ℚ) (O : Fin 2 → ℝ → ℝ) : ℝ :=
  twoPointConnectedCorrelation
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableMoment
      μ time O Finset.univ)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableMoment
      μ time O ({0} : Finset (Fin 2)))
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableMoment
      μ time O ({1} : Finset (Fin 2)))

/-- The same labelled two-point connected function formed from translated
moments. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalSlotShiftedTwoPointConnectedCorrelation
    (μ : Measure (ℚ → ℝ)) (time : Fin 2 → ℚ) (O : Fin 2 → ℝ → ℝ) (r : ℚ) : ℝ :=
  twoPointConnectedCorrelation
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableShiftedMoment
      μ time O Finset.univ r)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableShiftedMoment
      μ time O ({0} : Finset (Fin 2)) r)
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotObservableShiftedMoment
      μ time O ({1} : Finset (Fin 2)) r)

/-- Exact stationarity of the labelled connected two-point function, including
the repeated-time case. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_slotTwoPointConnectedCorrelation_shift_eq_self
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
    (time : Fin 2 → ℚ) (r : ℚ) (O : Fin 2 → ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalSlotShiftedTwoPointConnectedCorrelation
        L.continuumMeasure.toMeasure time O r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalSlotTwoPointConnectedCorrelation
        L.continuumMeasure.toMeasure time O := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalSlotShiftedTwoPointConnectedCorrelation
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalSlotTwoPointConnectedCorrelation
  apply twoPointConnectedCorrelation_congr
  · exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotObservableMoment_shift_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r O Finset.univ
  · exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotObservableMoment_shift_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r O
        ({0} : Finset (Fin 2))
  · exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotObservableMoment_shift_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r O
        ({1} : Finset (Fin 2))

/-- Rational-time connected Schwinger function for `n` labelled Euclidean
insertions. This is an OS-facing Euclidean object; no Minkowski or full real-time
continuation is asserted by this definition. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ) : ℝ :=
  periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotConnectedCorrelation
    μ time O Finset.univ

/-- Connected Schwinger function formed from a common rational translation of
all insertion times. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
    (μ : Measure (ℚ → ℝ)) (n : ℕ) (time : Fin n → ℚ) (O : Fin n → ℝ → ℝ)
    (r : ℚ) : ℝ :=
  periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftedConnectedCorrelation
    μ time O Finset.univ r

/-- Every finite connected Schwinger function is exactly invariant under common
rational translation of all labelled insertion times. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
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
    (n : ℕ) (time : Fin n → ℚ) (r : ℚ) (O : Fin n → ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time O := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotConnectedCorrelation_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r O Finset.univ

/-- Bare-coordinate connected Schwinger stationarity, obtained by using the
identity observable at every labelled slot. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedCoordinateSchwinger_shift_eq_self
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
    (n : ℕ) (time : Fin n → ℚ) (r : ℚ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalShiftedConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time (fun _ x => x) r =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalConnectedSchwingerFunction
        L.continuumMeasure.toMeasure n time (fun _ x => x) := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_connectedSchwinger_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L n time r
      (fun _ x => x)

end

end MathlibAnalytic
end MGAP4D
