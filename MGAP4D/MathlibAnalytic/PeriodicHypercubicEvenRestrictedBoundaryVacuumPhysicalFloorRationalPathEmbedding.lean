import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProjectiveLaw
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalPathNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The physical rational-time skeleton read directly from one actual finite
Wilson configuration.

At scale `n`, rational physical time `q` is read at the canonical lattice step
`⌊q / a_n⌋`.  The carrier `ℚ → ℝ` is countably indexed and hence belongs to the
existing Polish-product infrastructure, unlike the full uncountable carrier
`ℝ → ℝ`. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℚ → ℝ :=
  fun q =>
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
      H N hN beta hbeta
      (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) A

/-- The rational-time floor readout is measurable into the countable product
Borel space. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n) := by
  exact measurable_pi_lambda _ (fun q =>
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_measurable
      H N hN beta hbeta
      (physicalTemporalFloorStep latticeSpacing (q : ℝ) n))

/-- The finite rational-time path law, directly pushed forward from the actual
finite Wilson Gibbs measure. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) : Measure (ℚ → ℝ) :=
  Measure.map
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
      H N hN beta hbeta latticeSpacing n)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure

/-- The same same-source rational path law with normalization retained by
construction. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) : ProbabilityMeasure (ℚ → ℝ) :=
  (periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsProbabilityMeasure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_measurable
        H N hN beta hbeta latticeSpacing n).aemeasurable

@[simp]
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n : Measure (ℚ → ℝ)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  rfl

/-- Audit-visible same-root identity: the entire rational-time physical skeleton
is read directly from the same actual finite Wilson Gibbs configuration. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_eq_map_wilson
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
          H N hN beta hbeta latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  rfl

/-- Every rational physical-time coordinate has exactly the already constructed
effective-boundary scalar law.  No real-time stationarity assumption is used:
the floor selector merely chooses one integer coordinate of the stationary
finite Wilson path. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_coordinate_eq_map_effectiveMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (q : ℚ) :
    Measure.map (fun x : ℚ → ℝ => x q)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
  calc
    Measure.map (fun x : ℚ → ℝ => x q)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
            H N hN beta hbeta latticeSpacing n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      Measure.map
        ((fun x : ℚ → ℝ => x q) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
            H N hN beta hbeta latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      Measure.map_map
        (measurable_pi_apply q)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_measurable
          H N hN beta hbeta latticeSpacing n)
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
          H N hN beta hbeta
          (physicalTemporalFloorStep latticeSpacing (q : ℝ) n))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      rfl
    _ = Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) :=
      periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_map_gibbsMeasure_eq_map_effectiveMeasure
        H N hN beta hbeta
        (physicalTemporalFloorStep latticeSpacing (q : ℝ) n)

/-- The rational floor skeleton supplies a fixed countable-product Polish
physical carrier for all lattice scales.

The interpolation is still a direct readout from the actual finite Wilson
configuration.  This creates no continuum real-time action and makes no
regularity assumption beyond the existing measurable finite readout. -/
@[reducible] noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop) :
    ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding where
  PhysicalConfiguration := ℚ → ℝ
  system := fun n =>
    periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (H n)) N hN
      (beta n) (hbeta n)
  interpolate := fun n A =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
      (H n) N hN (beta n) (hbeta n) latticeSpacing n A
  interpolate_measurable := fun n =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_measurable
      (H n) N hN (beta n) (hbeta n) latticeSpacing n
  latticeSpacing := latticeSpacing
  latticeSpacing_pos := latticeSpacing_pos
  latticeSpacing_tendsto_zero := latticeSpacing_tendsto_zero
  physicalVolume := physicalVolume
  physicalVolume_tendsto_atTop := physicalVolume_tendsto_atTop

/-- The generic embedded probability law of the rational Polish carrier is
exactly the direct same-Wilson-source rational floor path law at that scale. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure n =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
        (H n) N hN (beta n) (hbeta n) latticeSpacing n := by
  rfl

end

end MathlibAnalytic
end MGAP4D
