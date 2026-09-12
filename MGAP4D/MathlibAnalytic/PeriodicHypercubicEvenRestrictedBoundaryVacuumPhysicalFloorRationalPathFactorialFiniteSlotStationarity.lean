import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialContinuumStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteSlotNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteSlotTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteSlotCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteSlotSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteSlotMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteSlotBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Read a rational continuum path at a family of labelled slots.

The time labelling `time : ι → ℚ` is not required to be injective. Distinct
slots may therefore carry different observables at the same rational time. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout
    {ι : Type*} (time : ι → ℚ) (x : ℚ → ℝ) : ι → ℝ :=
  fun i => x (time i)

/-- Read the same labelled slots after one common rational time translation. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
    {ι : Type*} (time : ι → ℚ) (r : ℚ) (x : ℚ → ℝ) : ι → ℝ :=
  fun i => x (time i + r)

/-- Labelled slot readout is measurable, with no injectivity hypothesis on the
time labelling. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout_measurable
    {ι : Type*} (time : ι → ℚ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply (time i))

/-- Commonly translated labelled slot readout is measurable. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout_measurable
    {ι : Type*} (time : ι → ℚ) (r : ℚ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
        time r) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply (time i + r))

/-- Slot translation is exactly slot readout after full rational path
translation. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout_eq_readout_shift
    {ι : Type*} (time : ι → ℚ) (r : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
        time r x =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout
        time
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r x) := by
  rfl

/-- Full rational path-law stationarity projects to exact stationarity of every
labelled slot joint law.

Unlike a `Finset ℚ` readout, this API retains slot multiplicity: two different
slots may have the same rational time while carrying different downstream
observables. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotJointLaw_shift_eq_self
    {ι : Type*}
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
    (time : ι → ℚ) (r : ℚ) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
          time r)
        L.continuumMeasure.toMeasure =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time)
        L.continuumMeasure.toMeasure := by
  have hReadout :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout_measurable
      time
  have hShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r
  have hStationaryProbability :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L r
  have hStationaryMeasure :
      Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          L.continuumMeasure.toMeasure =
        L.continuumMeasure.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hStationaryProbability
    simpa only [ProbabilityMeasure.toMeasure_map] using h
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
          time r)
        L.continuumMeasure.toMeasure =
      Measure.map
        ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
        L.continuumMeasure.toMeasure := by
      apply congrArg (fun f => Measure.map f L.continuumMeasure.toMeasure)
      funext x
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout_eq_readout_shift
          time r x
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          L.continuumMeasure.toMeasure) :=
      (Measure.map_map hReadout hShift).symm
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time)
        L.continuumMeasure.toMeasure := by
      exact congrArg
        (fun μ =>
          Measure.map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time)
            μ)
        hStationaryMeasure

/-- Every Bochner-valued observable of the labelled slot vector has exactly the
same integral against the translated and untranslated slot laws. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotIntegral_shift_eq_self
    {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
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
    (time : ι → ℚ) (r : ℚ) (F : (ι → ℝ) → E) :
    (∫ y, F y ∂
        Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotShiftReadout
            time r)
          L.continuumMeasure.toMeasure) =
      ∫ y, F y ∂
        Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteSlotReadout time)
          L.continuumMeasure.toMeasure := by
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteSlotJointLaw_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L time r]

end

end MathlibAnalytic
end MGAP4D
