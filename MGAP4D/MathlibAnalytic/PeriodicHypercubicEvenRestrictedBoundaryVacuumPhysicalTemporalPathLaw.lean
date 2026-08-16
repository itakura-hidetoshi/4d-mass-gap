import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalLaw

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumTemporalPathLawNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalPathLawTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalPathLawCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalPathLawSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalPathLawMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalPathLawBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The complete integer-time scalar path read from one actual finite Wilson
configuration. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℤ → ℝ :=
  fun t =>
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
      H N hN beta hbeta t A

/-- The full integer-time path readout is measurable for the product Borel
structure on `ℤ → ℝ`. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
        H N hN beta hbeta) := by
  exact measurable_pi_lambda _ (fun t =>
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_measurable
      H N hN beta hbeta t)

/-- Integer translation of a scalar temporal path.  The sign convention is
chosen so that shifting a translated finite configuration back to the reference
path is exactly the covariance theorem proved above. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
    (k : ℤ) (x : ℤ → ℝ) : ℤ → ℝ :=
  fun t => x (t + k)

/-- Integer temporal path shifts are measurable. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_measurable
    (k : ℤ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply (t + k))

@[simp]
theorem periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_zero
    (x : ℤ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift 0 x = x := by
  funext t
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift]

/-- The path shifts form the expected additive integer action. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_add
    (k l : ℤ) (x : ℤ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift (k + l) x =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift l x) := by
  funext t
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift, add_assoc]

/-- Exact finite covariance packaged on the full scalar path: translating the
Wilson configuration by `k` and the resulting scalar path by the same `k`
returns the original path. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_shift_translation
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
          H N hN beta hbeta
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength H) k A)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
        H N hN beta hbeta A := by
  funext t
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_integerTemporal_covariant
      H N hN beta hbeta t k A

/-- Equivalently, shifting the path of an untranslated configuration by `k`
is the path of the configuration translated by `-k`. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_readout_eq_translation_neg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
          H N hN beta hbeta A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
        H N hN beta hbeta
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) (-k) A) := by
  funext t
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
  have hindex : -(t + k) = -t + (-k) := by omega
  rw [hindex]
  rw [periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply]

/-- The complete integer-time scalar path law obtained directly as a pushforward
of the normalized finite Wilson Gibbs measure.  No Kolmogorov extension is
needed at this finite scale because all temporal coordinates are read from one
common Wilson configuration. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure (ℤ → ℝ) :=
  Measure.map
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
      H N hN beta hbeta)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure

/-- The full temporal path law is a probability measure because its source is
the normalized Wilson Gibbs law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
        H N hN beta hbeta) := by
  letI : IsProbabilityMeasure
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
    inferInstance
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
  exact Measure.isProbabilityMeasure_map
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
      H N hN beta hbeta).aemeasurable

/-- The actual finite Wilson temporal path law is exactly stationary under every
integer path shift.

This is generated from the concrete path covariance and exact Gibbs translation
invariance.  No stationarity or continuum time-action premise is introduced. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_map_shift_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℤ) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
        H N hN beta hbeta := by
  have hPath :=
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
      H N hN beta hbeta
  have hShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_measurable k
  have hTranslate :
      Measurable
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) (-k)) :=
    (periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-k)).measurable
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift k ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      Measure.map_map hShift hPath
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta ∘
          periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength H) (-k))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure)
      funext A
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_readout_eq_translation_neg
          H N hN beta hbeta k A
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
          H N hN beta hbeta)
        (Measure.map
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength H) (-k))
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      (Measure.map_map hPath hTranslate).symm
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
          H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      rw [periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta (-k)]
      rfl

/-- Every coordinate of the full path law is exactly the corresponding
integer-time scalar Wilson pushforward law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_coordinate_eq_timeLaw
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (t : ℤ) :
    Measure.map (fun x : ℤ → ℝ => x t)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
          H N hN beta hbeta t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
  rw [Measure.map_map
    (measurable_pi_apply t)
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
      H N hN beta hbeta)]
  rfl

/-- Hence every coordinate marginal of the stationary full path law is the same
literal effective-boundary scalar law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_coordinate_eq_map_effectiveMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (t : ℤ) :
    Measure.map (fun x : ℤ → ℝ => x t)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) := by
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_coordinate_eq_timeLaw]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_map_gibbsMeasure_eq_map_effectiveMeasure
      H N hN beta hbeta t

end

end MathlibAnalytic
end MGAP4D
