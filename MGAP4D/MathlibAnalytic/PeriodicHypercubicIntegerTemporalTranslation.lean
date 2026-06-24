import MGAP4D.MathlibAnalytic.PeriodicHypercubicTranslationInvariance
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance integerTemporalIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance integerTemporalCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance integerTemporalSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance integerTemporalMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance integerTemporalBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- The periodic displacement by `k` lattice units in the distinguished temporal
coordinate `0`.  The remaining three coordinates are fixed. -/
def periodicHypercubicIntegerTemporalDisplacement
    (n : ℕ) (k : ℤ) : PeriodicHypercubicVertex n :=
  fun mu => if mu = (0 : Fin 4) then (k : ZMod n) else 0

@[simp]
theorem periodicHypercubicIntegerTemporalDisplacement_time
    (n : ℕ) (k : ℤ) :
    periodicHypercubicIntegerTemporalDisplacement n k 0 = (k : ZMod n) := by
  simp [periodicHypercubicIntegerTemporalDisplacement]

@[simp]
theorem periodicHypercubicIntegerTemporalDisplacement_space
    (n : ℕ) (k : ℤ) (mu : Fin 4) (hmu : mu ≠ 0) :
    periodicHypercubicIntegerTemporalDisplacement n k mu = 0 := by
  simp [periodicHypercubicIntegerTemporalDisplacement, hmu]

@[simp]
theorem periodicHypercubicIntegerTemporalDisplacement_zero
    (n : ℕ) :
    periodicHypercubicIntegerTemporalDisplacement n 0 = 0 := by
  ext mu
  by_cases hmu : mu = (0 : Fin 4) <;>
    simp [periodicHypercubicIntegerTemporalDisplacement, hmu]

@[simp]
theorem periodicHypercubicIntegerTemporalDisplacement_add
    (n : ℕ) (k l : ℤ) :
    periodicHypercubicIntegerTemporalDisplacement n (k + l) =
      periodicHypercubicIntegerTemporalDisplacement n k +
        periodicHypercubicIntegerTemporalDisplacement n l := by
  ext mu
  by_cases hmu : mu = (0 : Fin 4) <;>
    simp [periodicHypercubicIntegerTemporalDisplacement, hmu, Int.cast_add]

@[simp]
theorem periodicHypercubicIntegerTemporalDisplacement_neg
    (n : ℕ) (k : ℤ) :
    periodicHypercubicIntegerTemporalDisplacement n (-k) =
      -periodicHypercubicIntegerTemporalDisplacement n k := by
  ext mu
  by_cases hmu : mu = (0 : Fin 4) <;>
    simp [periodicHypercubicIntegerTemporalDisplacement, hmu]

/-- Configuration translation by an integer number of temporal lattice units. -/
noncomputable def periodicHypercubicIntegerTemporalConfigurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (k : ℤ) :
    (PeriodicHypercubicEdge n → Gauge) ≃ᵐ
      (PeriodicHypercubicEdge n → Gauge) :=
  periodicHypercubicConfigurationTranslationMeasurableEquiv n
    (periodicHypercubicIntegerTemporalDisplacement n k)

@[simp]
theorem periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (k : ℤ)
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicIntegerTemporalConfigurationTranslation n k A
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n k) e) =
      A e :=
  periodicHypercubicConfigurationTranslation_apply_translatedEdge
    n (periodicHypercubicIntegerTemporalDisplacement n k) A e

/-- Every concrete integer temporal translation preserves the canonical finite
periodic `SU(N)` Wilson Gibbs law. -/
theorem periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (k : ℤ) :
    MeasureTheory.Measure.map
      (periodicHypercubicIntegerTemporalConfigurationTranslation
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n k)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure =
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).gibbsMeasure :=
  periodicHypercubicSpecialUnitary_gibbs_map_translation_eq_self
    n N hN beta beta_nonneg
    (periodicHypercubicIntegerTemporalDisplacement n k)

end

end MathlibAnalytic
end MGAP4D
