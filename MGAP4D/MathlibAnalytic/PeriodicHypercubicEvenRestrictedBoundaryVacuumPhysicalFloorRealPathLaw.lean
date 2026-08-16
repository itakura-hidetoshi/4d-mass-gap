import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorTemporalPathStationarity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRealPathNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRealPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRealPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRealPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRealPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRealPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Extend an integer-indexed scalar path to every physical real time by the
canonical scale-wise floor selector.

This is a deterministic readout from the already constructed discrete path. It
does not assert continuity of the resulting real-indexed sample path. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (x : ℤ → ℝ) : ℝ → ℝ :=
  fun t => x (physicalTemporalFloorStep latticeSpacing t n)

/-- The deterministic floor extension is measurable for the product sigma
algebras on the integer- and real-indexed path spaces. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
        latticeSpacing n) := by
  exact measurable_pi_lambda _ (fun t =>
    measurable_pi_apply (physicalTemporalFloorStep latticeSpacing t n))

/-- Translation of a real-indexed scalar path. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
    (s : ℝ) (x : ℝ → ℝ) : ℝ → ℝ :=
  fun t => x (t + s)

/-- Every real path shift is measurable for the product sigma algebra. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_measurable
    (s : ℝ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply (t + s))

@[simp]
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_zero
    (x : ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift 0 x = x := by
  funext t
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift]

/-- Real path shifts satisfy the additive action law. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_add
    (s r : ℝ) (x : ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift (s + r) x =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift r x) := by
  funext t
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift,
    add_assoc]

/-- Adding an exact lattice-time multiple before applying the floor selector is
exactly addition of the corresponding integer step. -/
theorem physicalTemporalFloorStep_add_lattice_multiple
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ) (n : ℕ) (k : ℤ) :
    physicalTemporalFloorStep latticeSpacing
        (t + (k : ℝ) * latticeSpacing n) n =
      physicalTemporalFloorStep latticeSpacing t n + k := by
  unfold physicalTemporalFloorStep
  have hne : latticeSpacing n ≠ 0 := ne_of_gt (latticeSpacing_pos n)
  have hquot :
      (t + (k : ℝ) * latticeSpacing n) / latticeSpacing n =
        t / latticeSpacing n + (k : ℝ) := by
    field_simp [hne]
  rw [hquot, Int.floor_add_intCast]

/-- The real floor extension exactly intertwines an integer path shift with the
corresponding physical lattice-time shift.

Hence the real-indexed carrier receives its finite-scale temporal covariance
constructively from the discrete action rather than from a new real-time
stationarity premise. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_floorExtension
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (k : ℤ) (x : ℤ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
        ((k : ℝ) * latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n x) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
        latticeSpacing n
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k x) := by
  funext t
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
  rw [physicalTemporalFloorStep_add_lattice_multiple
    latticeSpacing latticeSpacing_pos t n k]

/-- The full real-indexed floor path law is the deterministic pushforward of the
actual stationary integer path law at one finite scale. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    Measure (ℝ → ℝ) :=
  Measure.map
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
      latticeSpacing n)
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
      H N hN beta hbeta)

/-- The same floor-extended path law bundled as a normalized Mathlib probability
measure. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure (ℝ → ℝ) :=
  (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure
    H N hN beta hbeta).map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
        latticeSpacing n).aemeasurable

@[simp]
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n : Measure (ℝ → ℝ)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  rfl

/-- The real-indexed floor path law remains a probability measure by direct
pushforward from the normalized discrete path law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n) := by
  rw [←
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure_toMeasure
      H N hN beta hbeta latticeSpacing n]
  infer_instance

/-- Audit-visible same-root identity: the real-indexed floor path law is still
a direct deterministic pushforward of the very same actual finite Wilson Gibbs
measure. No finite-scale Kolmogorov extension is inserted. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_eq_map_wilson
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
  exact Measure.map_map
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
      latticeSpacing n)
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
      H N hN beta hbeta)

/-- At finite scale the real-indexed floor path law is exactly stationary under
every physical shift belonging to the lattice subgroup `a_n ℤ`.

Only discrete Wilson stationarity and the exact floor intertwining identity are
used; invariance under arbitrary real shifts is not asserted. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_map_latticeShift_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (k : ℤ) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
          ((k : ℝ) * latticeSpacing n))
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  have hExtension :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
      latticeSpacing n
  have hRealShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_measurable
      ((k : ℝ) * latticeSpacing n)
  have hIntegerShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_measurable k
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
          ((k : ℝ) * latticeSpacing n))
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
            ((k : ℝ) * latticeSpacing n) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) :=
      Measure.map_map hRealShift hExtension
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta))
      funext x
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_floorExtension
          latticeSpacing latticeSpacing_pos n k x
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k)
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) :=
      (Measure.map_map hExtension hIntegerShift).symm
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      rw [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_map_shift_eq_self]

/-- Every real-time coordinate of the finite floor-extended process has exactly
the same effective-boundary scalar law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_coordinate_eq_map_effectiveMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    Measure.map (fun x : ℝ → ℝ => x t)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) := by
  have hExtension :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
      latticeSpacing n
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
  calc
    Measure.map (fun x : ℝ → ℝ => x t)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) =
      Measure.map
        ((fun x : ℝ → ℝ => x t) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) :=
      Measure.map_map (measurable_pi_apply t) hExtension
    _ = Measure.map
        (fun x : ℤ → ℝ =>
          x (physicalTemporalFloorStep latticeSpacing t n))
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) := by
      rfl
    _ = Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) :=
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_coordinate_eq_map_effectiveMeasure
        H N hN beta hbeta
        (physicalTemporalFloorStep latticeSpacing t n)

end

end MathlibAnalytic
end MGAP4D
