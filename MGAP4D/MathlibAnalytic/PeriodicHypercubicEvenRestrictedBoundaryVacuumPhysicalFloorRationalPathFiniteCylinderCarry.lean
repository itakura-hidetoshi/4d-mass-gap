import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftAction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathCylinderCarryLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalCylinderCarryNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalCylinderCarryTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalCylinderCarryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalCylinderCarrySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalCylinderCarryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalCylinderCarryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Restrict the same integer-time boundary-vacuum path to physical rational
coordinates through the canonical scale-wise floor selector.

This is deterministic and keeps every rational coordinate on one common
integer path. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (x : ℤ → ℝ) : ℚ → ℝ :=
  fun q => x (physicalTemporalFloorStep latticeSpacing (q : ℝ) n)

/-- The rational floor extension is measurable into the countable product
Borel space. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension_measurable
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
        latticeSpacing n) := by
  exact measurable_pi_lambda _ (fun q =>
    measurable_pi_apply (physicalTemporalFloorStep latticeSpacing (q : ℝ) n))

/-- The direct rational Wilson readout is definitionally the rational floor
extension of the full integer temporal readout from the same configuration. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_eq_extension_temporalPathReadout
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n A =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
        latticeSpacing n
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
          H N hN beta hbeta A) := by
  rfl

/-- Same-root factorization of the whole finite rational path law through the
actual stationary integer temporal path law.

No coordinate independence and no Kolmogorov reconstruction are used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_eq_map_temporalPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
          latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
          H N hN beta hbeta latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
            latticeSpacing n ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure)
      funext A
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_eq_extension_temporalPathReadout
          H N hN beta hbeta latticeSpacing n A
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
          latticeSpacing n)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      (Measure.map_map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension_measurable
          latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
          H N hN beta hbeta)).symm

/-- After removing the common floor shift corresponding to a rational
translation `r`, the residual finite rational cylinder consists exactly of the
coordinatewise binary floor carries. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (r : ℚ) (J : Finset ℚ)
    (x : ℤ → ℝ) : ∀ q : J, ℝ :=
  fun q =>
    x
      (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n +
        physicalTemporalFloorCarry latticeSpacing ((q : ℚ) : ℝ) (r : ℝ) n)

/-- The residual rational-cylinder readout is measurable because every output
coordinate is one evaluation coordinate of the common integer path. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout_measurable
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (r : ℚ) (J : Finset ℚ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
        latticeSpacing n r J) := by
  exact measurable_pi_lambda _ (fun q =>
    measurable_pi_apply
      (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n +
        physicalTemporalFloorCarry latticeSpacing ((q : ℚ) : ℝ) (r : ℝ) n))

/-- Pointwise exact carry factorization on every finite rational-time cylinder.

The common integer shift `floor(r/a_n)` is separated from the coordinatewise
binary carry.  This identity is simultaneous in all coordinates of `J`, so it
preserves their joint dependence. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_restrict_shift_extension_eq_residual_shift
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (r : ℚ) (J : Finset ℚ)
    (x : ℤ → ℝ) :
    J.restrict (π := fun _ : ℚ => ℝ)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
            latticeSpacing n x)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
        latticeSpacing n r J
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
          (physicalTemporalFloorStep latticeSpacing (r : ℝ) n) x) := by
  ext q
  change
    x (physicalTemporalFloorStep latticeSpacing ((((q : ℚ) + r : ℚ) : ℝ)) n) =
      x
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n +
          physicalTemporalFloorCarry latticeSpacing ((q : ℚ) : ℝ) (r : ℝ) n +
          physicalTemporalFloorStep latticeSpacing (r : ℝ) n)
  have hcast : ((((q : ℚ) + r : ℚ) : ℝ)) =
      ((q : ℚ) : ℝ) + (r : ℝ) := by
    norm_num
  rw [hcast, physicalTemporalFloorStep_add_eq_add_add_carry]
  congr 1
  omega

/-- The finite rational-cylinder law after a fixed rational path translation. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftedFiniteMarginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (r : ℚ) (J : Finset ℚ) :
    Measure (∀ q : J, ℝ) :=
  Measure.map (J.restrict (π := fun _ : ℚ => ℝ))
    (Measure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n))

/-- Exact same-root finite rational-cylinder carry identity.

At finite lattice scale, exact integer temporal stationarity removes the common
floor shift selected by `r`.  The complete remaining discrepancy from rational
path stationarity is the coordinatewise binary carry on the same integer path.
No one-coordinate argument is used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftedFiniteMarginal_eq_residual
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (r : ℚ) (J : Finset ℚ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftedFiniteMarginal
        H N hN beta hbeta latticeSpacing n r J =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
          latticeSpacing n r J)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
  have hJ : Measurable (J.restrict (π := fun _ : ℚ => ℝ)) :=
    J.measurable_restrict
  have hRationalShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r
  have hExtension :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension_measurable
      latticeSpacing n
  have hResidual :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout_measurable
      latticeSpacing n r J
  have hIntegerShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_measurable
      (physicalTemporalFloorStep latticeSpacing (r : ℝ) n)
  unfold
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftedFiniteMarginal
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_eq_map_temporalPathMeasure]
  calc
    Measure.map (J.restrict (π := fun _ : ℚ => ℝ))
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          (Measure.map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
              latticeSpacing n)
            (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
              H N hN beta hbeta))) =
      Measure.map
        (J.restrict (π := fun _ : ℚ => ℝ) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
            latticeSpacing n)
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) :=
      Measure.map_map hJ hRationalShift
    _ = Measure.map
        ((J.restrict (π := fun _ : ℚ => ℝ) ∘
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathExtension
            latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) :=
      Measure.map_map (hJ.comp hRationalShift) hExtension
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
            latticeSpacing n r J ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
            (physicalTemporalFloorStep latticeSpacing (r : ℝ) n))
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta))
      funext x
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_restrict_shift_extension_eq_residual_shift
          latticeSpacing n r J x
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
          latticeSpacing n r J)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
            (physicalTemporalFloorStep latticeSpacing (r : ℝ) n))
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) :=
      (Measure.map_map hResidual hIntegerShift).symm
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinderReadout
          latticeSpacing n r J)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      rw [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_map_shift_eq_self]

/-- Every coordinate of the residual rational cylinder still represents its
original physical rational time along the same strict subsequence. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinder_physicalTime_tendsto_subsequence
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (r : ℚ) (J : Finset ℚ) (q : J) :
    Tendsto
      (fun n : ℕ =>
        (((physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) (subsequence n) +
            physicalTemporalFloorCarry latticeSpacing ((q : ℚ) : ℝ) (r : ℝ)
              (subsequence n) : ℤ) : ℝ) *
          latticeSpacing (subsequence n)))
      atTop (nhds (((q : ℚ) : ℝ))) := by
  exact
    physicalTemporalFloorStep_add_carry_physicalTime_tendsto_subsequence
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      subsequence hsubsequence ((q : ℚ) : ℝ) (r : ℝ)

/-- The whole finite vector of carry-corrected physical rational times converges
coordinatewise on one common subsequence. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinder_physicalTimes_tendsto_subsequence
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (r : ℚ) (J : Finset ℚ) :
    Tendsto
      (fun n : ℕ => fun q : J =>
        (((physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) (subsequence n) +
            physicalTemporalFloorCarry latticeSpacing ((q : ℚ) : ℝ) (r : ℝ)
              (subsequence n) : ℤ) : ℝ) *
          latticeSpacing (subsequence n)))
      atTop
      (nhds (fun q : J => (((q : ℚ) : ℝ)))) := by
  rw [tendsto_pi_nhds]
  intro q
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathResidualCylinder_physicalTime_tendsto_subsequence
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      subsequence hsubsequence r J q

end

end MathlibAnalytic
end MGAP4D
