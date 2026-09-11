import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProjectiveLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathCarry

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRealCylinderCarryNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRealCylinderCarryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRealCylinderCarryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRealCylinderCarrySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRealCylinderCarryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRealCylinderCarryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- After removing the common floor shift associated with a real translation
`s`, the only remaining finite-cylinder readout is the coordinatewise binary
carry. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (s : ℝ) (J : Finset ℝ)
    (x : ℤ → ℝ) : ∀ t : J, ℝ :=
  fun t =>
    x
      (physicalTemporalFloorStep latticeSpacing (t : ℝ) n +
        physicalTemporalFloorCarry latticeSpacing (t : ℝ) s n)

/-- The residual finite-cylinder readout is measurable because every output
coordinate is one evaluation coordinate of the discrete path. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout_measurable
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (s : ℝ) (J : Finset ℝ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
        latticeSpacing n s J) := by
  exact measurable_pi_lambda _ (fun t =>
    measurable_pi_apply
      (physicalTemporalFloorStep latticeSpacing (t : ℝ) n +
        physicalTemporalFloorCarry latticeSpacing (t : ℝ) s n))

/-- Pointwise exact carry factorization on every finite real-time cylinder.

The common integer shift `floor(s/a_n)` is separated from the coordinatewise
carry, which is already known to be only `0` or `1`. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPath_restrict_shift_extension_eq_residual_shift
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (s : ℝ) (J : Finset ℝ)
    (x : ℤ → ℝ) :
    J.restrict (π := fun _ : ℝ => ℝ)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n x)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
        latticeSpacing n s J
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
          (physicalTemporalFloorStep latticeSpacing s n) x) := by
  ext t
  change
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n x) (t : ℝ) =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
        (physicalTemporalFloorStep latticeSpacing s n) x
        (physicalTemporalFloorStep latticeSpacing (t : ℝ) n +
          physicalTemporalFloorCarry latticeSpacing (t : ℝ) s n)
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_floorExtension_apply_carry]
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift,
    add_assoc, add_comm, add_left_comm]

/-- The finite-cylinder law after an arbitrary real translation. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathShiftedFiniteMarginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (s : ℝ) (J : Finset ℝ) :
    Measure (∀ t : J, ℝ) :=
  Measure.map (J.restrict (π := fun _ : ℝ => ℝ))
    (Measure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n))

/-- Exact arbitrary-real-shift cylinder identity.

At a finite lattice scale, discrete stationarity removes the common integer
shift selected by `s`. The whole discrepancy from genuine real-time
stationarity is therefore the coordinatewise binary carry and nothing else.
No continuum stationarity or real-time dynamics premise is used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathShiftedFiniteMarginal_eq_residual
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (s : ℝ) (J : Finset ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathShiftedFiniteMarginal
        H N hN beta hbeta latticeSpacing n s J =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
          latticeSpacing n s J)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
  have hJ :
      Measurable (J.restrict (π := fun _ : ℝ => ℝ)) :=
    J.measurable_restrict
  have hRealShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_measurable s
  have hExtension :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
      latticeSpacing n
  have hResidual :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout_measurable
      latticeSpacing n s J
  have hIntegerShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_measurable
      (physicalTemporalFloorStep latticeSpacing s n)
  unfold
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathShiftedFiniteMarginal
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
  calc
    Measure.map (J.restrict (π := fun _ : ℝ => ℝ))
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s)
          (Measure.map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
              latticeSpacing n)
            (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
              H N hN beta hbeta))) =
      Measure.map
        (J.restrict (π := fun _ : ℝ => ℝ) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) :=
      Measure.map_map hJ hRealShift
    _ = Measure.map
        ((J.restrict (π := fun _ : ℝ => ℝ) ∘
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) :=
      Measure.map_map (hJ.comp hRealShift) hExtension
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
            latticeSpacing n s J ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
            (physicalTemporalFloorStep latticeSpacing s n))
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta))
      funext x
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPath_restrict_shift_extension_eq_residual_shift
          latticeSpacing n s J x
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
          latticeSpacing n s J)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
            (physicalTemporalFloorStep latticeSpacing s n))
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) :=
      (Measure.map_map hResidual hIntegerShift).symm
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinderReadout
          latticeSpacing n s J)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      rw [
        periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_map_shift_eq_self]

end

end MathlibAnalytic
end MGAP4D
