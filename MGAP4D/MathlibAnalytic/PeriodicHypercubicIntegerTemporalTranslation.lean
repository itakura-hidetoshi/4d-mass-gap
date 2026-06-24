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
coordinate indexed by `0`.  The remaining three coordinates are fixed. -/
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

@[simp]
theorem periodicHypercubicIntegerTemporalEdgeTranslation_zero_apply
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeTranslationEquiv n
        (periodicHypercubicIntegerTemporalDisplacement n 0) e = e := by
  cases e
  simp [periodicHypercubicEdgeTranslationEquiv]

/-- Integer temporal edge translations compose according to integer addition. -/
theorem periodicHypercubicIntegerTemporalEdgeTranslation_add_apply
    (n : ℕ) (k l : ℤ) (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeTranslationEquiv n
        (periodicHypercubicIntegerTemporalDisplacement n (k + l)) e =
      periodicHypercubicEdgeTranslationEquiv n
        (periodicHypercubicIntegerTemporalDisplacement n k)
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n l) e) := by
  apply Prod.ext
  · change e.1 + periodicHypercubicIntegerTemporalDisplacement n (k + l) =
      (e.1 + periodicHypercubicIntegerTemporalDisplacement n l) +
        periodicHypercubicIntegerTemporalDisplacement n k
    rw [periodicHypercubicIntegerTemporalDisplacement_add]
    abel
  · rfl

/-- The zero integer temporal translation is the identity on configurations. -/
@[simp]
theorem periodicHypercubicIntegerTemporalConfigurationTranslation_zero_apply
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicIntegerTemporalConfigurationTranslation n 0 A = A := by
  funext e
  simpa using
    (periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
      n 0 A e)

/-- Integer temporal configuration translations compose according to integer
addition. -/
@[simp]
theorem periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (k l : ℤ) (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicIntegerTemporalConfigurationTranslation n (k + l) A =
      periodicHypercubicIntegerTemporalConfigurationTranslation n k
        (periodicHypercubicIntegerTemporalConfigurationTranslation n l A) := by
  funext e'
  obtain ⟨e, rfl⟩ :=
    (periodicHypercubicEdgeTranslationEquiv n
      (periodicHypercubicIntegerTemporalDisplacement n (k + l))).surjective e'
  calc
    periodicHypercubicIntegerTemporalConfigurationTranslation n (k + l) A
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n (k + l)) e) =
      A e :=
        periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
          n (k + l) A e
    _ = periodicHypercubicIntegerTemporalConfigurationTranslation n l A
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n l) e) :=
      (periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
        n l A e).symm
    _ = periodicHypercubicIntegerTemporalConfigurationTranslation n k
        (periodicHypercubicIntegerTemporalConfigurationTranslation n l A)
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n k)
          (periodicHypercubicEdgeTranslationEquiv n
            (periodicHypercubicIntegerTemporalDisplacement n l) e)) :=
      (periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
        n k
        (periodicHypercubicIntegerTemporalConfigurationTranslation n l A)
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n l) e)).symm
    _ = periodicHypercubicIntegerTemporalConfigurationTranslation n k
        (periodicHypercubicIntegerTemporalConfigurationTranslation n l A)
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n (k + l)) e) := by
      rw [periodicHypercubicIntegerTemporalEdgeTranslation_add_apply]

/-- Integer temporal translations define an additive group action on periodic
configurations. -/
noncomputable instance periodicHypercubicIntegerTemporalConfigurationAddAction
    {Gauge : Type} [MeasurableSpace Gauge] (n : ℕ) :
    AddAction ℤ (PeriodicHypercubicEdge n → Gauge) where
  vadd k A := periodicHypercubicIntegerTemporalConfigurationTranslation n k A
  zero_vadd A :=
    periodicHypercubicIntegerTemporalConfigurationTranslation_zero_apply n A
  add_vadd k l A :=
    periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply n k l A

/-- Translation by `-k` is a left inverse of translation by `k`. -/
@[simp]
theorem periodicHypercubicIntegerTemporalConfigurationTranslation_neg_apply
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (k : ℤ) (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicIntegerTemporalConfigurationTranslation n (-k)
        (periodicHypercubicIntegerTemporalConfigurationTranslation n k A) = A := by
  simpa using
    (periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply
      n (-k) k A).symm

/-- Translation by `-k` is a right inverse of translation by `k`. -/
@[simp]
theorem periodicHypercubicIntegerTemporalConfigurationTranslation_apply_neg
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (k : ℤ) (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicIntegerTemporalConfigurationTranslation n k
        (periodicHypercubicIntegerTemporalConfigurationTranslation n (-k) A) = A := by
  simpa using
    (periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply
      n k (-k) A).symm

/-- Every concrete integer temporal translation preserves the canonical finite
periodic `SU(N)` Wilson Gibbs law. -/
theorem periodicHypercubicSpecialUnitary_gibbs_measurePreserving_integerTemporalTranslation
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (k : ℤ) :
    MeasurePreserving
      (periodicHypercubicIntegerTemporalConfigurationTranslation
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n k)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure :=
  periodicHypercubicSpecialUnitary_gibbs_measurePreserving_translation
    n N hN beta beta_nonneg
    (periodicHypercubicIntegerTemporalDisplacement n k)

/-- Pushforward form of integer temporal translation invariance. -/
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
  (periodicHypercubicSpecialUnitary_gibbs_measurePreserving_integerTemporalTranslation
    n N hN beta beta_nonneg k).map_eq

end

end MathlibAnalytic
end MGAP4D
