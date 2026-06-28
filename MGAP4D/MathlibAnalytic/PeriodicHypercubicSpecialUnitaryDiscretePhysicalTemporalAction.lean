import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPhysicalEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDiscreteTemporalAction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance discretePhysicalTemporalIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance discretePhysicalTemporalCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance discretePhysicalTemporalSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance discretePhysicalTemporalMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance discretePhysicalTemporalBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- At scale `n`, `k` integer temporal lattice steps represent physical time
`k * latticeSpacing n`. -/
noncomputable def periodicHypercubicPhysicalLatticeTime
    (latticeSpacing : ℕ → ℝ) (n : ℕ) : ℤ →+ ℝ where
  toFun k := (k : ℝ) * latticeSpacing n
  map_zero' := by simp
  map_add' k l := by
    rw [Int.cast_add]
    ring

@[simp]
theorem periodicHypercubicPhysicalLatticeTime_apply
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (k : ℤ) :
    periodicHypercubicPhysicalLatticeTime latticeSpacing n k =
      (k : ℝ) * latticeSpacing n :=
  rfl

/-- Construct the scale-separated temporal action for the canonical periodic
`SU(N)` Wilson embedding.

Only integer lattice steps are used at finite scale.  Their physical times are
`k * latticeSpacing n`.  Exact interpolation covariance is required only at
those realizable times, so no additive rounding map from `ℝ` to `ℤ` is assumed. -/
noncomputable def periodicHypercubicSpecialUnitaryDiscretePhysicalTemporalAction
    {PhysicalConfiguration : Type}
    [TopologicalSpace PhysicalConfiguration] [MeasurableSpace PhysicalConfiguration]
    [BorelSpace PhysicalConfiguration] [PolishSpace PhysicalConfiguration]
    (sideLength : ℕ → ℕ) (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ) (hN : 0 < N) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (beta_nonneg : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n,
      (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide (sideLength n) N
        (sideLength_pos n) hN (beta n) (beta_nonneg n)).base.Configuration →
        PhysicalConfiguration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (latticeSpacing : ℕ → ℝ) (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (physicalTranslate : ℝ → Homeomorph PhysicalConfiguration PhysicalConfiguration)
    (physicalTranslate_zero_apply : ∀ A, physicalTranslate 0 A = A)
    (physicalTranslate_add_apply : ∀ s t A,
      physicalTranslate (s + t) A = physicalTranslate s (physicalTranslate t A))
    (interpolate_integerTemporal_equivariant : ∀ n k U,
      interpolate n
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (sideLength n) k U) =
        physicalTranslate ((k : ℝ) * latticeSpacing n) (interpolate n U)) :
    (periodicHypercubicSpecialUnitaryPhysicalEmbedding
      sideLength sideLength_pos N hN beta beta_nonneg interpolate interpolate_measurable
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).PhysicalDiscreteTemporalAction := by
  exact
    { physicalTranslate := physicalTranslate
      physicalTranslate_zero_apply := physicalTranslate_zero_apply
      physicalTranslate_add_apply := physicalTranslate_add_apply
      latticeTime := periodicHypercubicPhysicalLatticeTime latticeSpacing
      latticeTranslate := fun n k =>
        periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (sideLength n) k
      latticeTranslate_measurable := fun n k =>
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (sideLength n) k).measurable
      latticeTranslate_zero_apply := fun n U =>
        periodicHypercubicIntegerTemporalConfigurationTranslation_zero_apply
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (sideLength n) U
      latticeTranslate_add_apply := fun n k l U =>
        periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (sideLength n) k l U
      latticeGibbs_map_eq_self := by
        intro n k
        letI : NeZero (sideLength n) :=
          ⟨Nat.ne_of_gt (sideLength_pos n)⟩
        change
          MeasureTheory.Measure.map
              (periodicHypercubicIntegerTemporalConfigurationTranslation
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
                (sideLength n) k)
              (periodicHypercubicSpecialUnitaryWilsonSystem
                (sideLength n) N hN (beta n) (beta_nonneg n)).gibbsMeasure =
            (periodicHypercubicSpecialUnitaryWilsonSystem
              (sideLength n) N hN (beta n) (beta_nonneg n)).gibbsMeasure
        exact
          periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
            (sideLength n) N hN (beta n) (beta_nonneg n) k
      interpolate_equivariant := by
        intro n k U
        exact interpolate_integerTemporal_equivariant n k U }

end

end MathlibAnalytic
end MGAP4D
