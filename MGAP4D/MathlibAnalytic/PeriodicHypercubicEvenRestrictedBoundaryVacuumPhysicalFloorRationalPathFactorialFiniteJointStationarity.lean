import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorialContinuumStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteJointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteJointTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteJointCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteJointSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteJointMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalFactorialFiniteJointBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Read a finite rational-time joint observable after one common rational
translation. Every output coordinate is evaluated on the same continuum path,
so all joint correlations are retained. -/
def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
    (J : Finset ℚ) (r : ℚ) (x : ℚ → ℝ) : ∀ q : J, ℝ :=
  fun q => x ((q : ℚ) + r)

/-- The translated finite joint readout is measurable. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout_measurable
    (J : Finset ℚ) (r : ℚ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
        J r) := by
  exact measurable_pi_lambda _ (fun q => measurable_pi_apply ((q : ℚ) + r))

/-- A translated finite joint readout is exactly finite restriction after the
full rational path translation. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout_eq_restrict_shift
    (J : Finset ℚ) (r : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
        J r x =
      J.restrict (π := fun _ : ℚ => ℝ)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r x) := by
  rfl

/-- Full rational path-law stationarity implies simultaneous translation
invariance of every finite rational-time joint law.

This is a genuine joint-law statement: it is obtained by pushing forward the
already constructed stationary continuum path measure, rather than by combining
one-coordinate marginals. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteJointLaw_shift_eq_self
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
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
          J r)
        (L.continuumMeasure : Measure (ℚ → ℝ)) =
      Measure.map
        (J.restrict (π := fun _ : ℚ => ℝ))
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  have hJ : Measurable (J.restrict (π := fun _ : ℚ => ℝ)) :=
    J.measurable_restrict
  have hShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r
  have hStationaryProbability :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L r
  have hStationaryMeasure :
      Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          (L.continuumMeasure : Measure (ℚ → ℝ)) =
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
    have h := congrArg ProbabilityMeasure.toMeasure hStationaryProbability
    simpa only [ProbabilityMeasure.toMeasure_map] using h
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
          J r)
        (L.continuumMeasure : Measure (ℚ → ℝ)) =
      Measure.map
        ((J.restrict (π := fun _ : ℚ => ℝ)) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      apply congrArg (fun f => Measure.map f (L.continuumMeasure : Measure (ℚ → ℝ)))
      funext x
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout_eq_restrict_shift
          J r x
    _ = Measure.map
        (J.restrict (π := fun _ : ℚ => ℝ))
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          (L.continuumMeasure : Measure (ℚ → ℝ))) :=
      (Measure.map_map hJ hShift).symm
    _ = Measure.map
        (J.restrict (π := fun _ : ℚ => ℝ))
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      rw [hStationaryMeasure]

/-- Consequently every measurable finite-cylinder readout has exactly the same
law after simultaneous rational translation of all of its time arguments.

No integrability or moment assumption is needed at this level. Downstream
OS/Wightman moment identities can therefore add only the integrability required
for their particular observable, while reusing this law equality unchanged. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_measurableCylinderLaw_shift_eq_self
    {α : Type*} [MeasurableSpace α]
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
    (F : (∀ q : J, ℝ) → α) (hF : Measurable F) :
    Measure.map
        (F ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
            J r)
        (L.continuumMeasure : Measure (ℚ → ℝ)) =
      Measure.map
        (F ∘ J.restrict (π := fun _ : ℚ => ℝ))
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  have hJoint :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finiteJointLaw_shift_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L J r
  have hShiftedJoint :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout_measurable
      J r
  have hJ : Measurable (J.restrict (π := fun _ : ℚ => ℝ)) :=
    J.measurable_restrict
  calc
    Measure.map
        (F ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
            J r)
        (L.continuumMeasure : Measure (ℚ → ℝ)) =
      Measure.map F
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointShiftReadout
            J r)
          (L.continuumMeasure : Measure (ℚ → ℝ))) :=
      (Measure.map_map hF hShiftedJoint).symm
    _ = Measure.map F
        (Measure.map
          (J.restrict (π := fun _ : ℚ => ℝ))
          (L.continuumMeasure : Measure (ℚ → ℝ))) := by
      rw [hJoint]
    _ = Measure.map
        (F ∘ J.restrict (π := fun _ : ℚ => ℝ))
        (L.continuumMeasure : Measure (ℚ → ℝ)) :=
      Measure.map_map hF hJ

end

end MathlibAnalytic
end MGAP4D
