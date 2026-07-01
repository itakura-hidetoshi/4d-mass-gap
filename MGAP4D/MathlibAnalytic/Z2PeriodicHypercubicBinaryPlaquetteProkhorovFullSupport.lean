import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteProkhorovNondegeneracy
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- The two singleton masses of a probability measure on `Bool` sum to one. -/
theorem probabilityMeasure_bool_singleton_sum
    (μ : ProbabilityMeasure Bool) :
    (μ : Measure Bool) {false} + (μ : Measure Bool) {true} = 1 := by
  have hUnion : ({false} : Set Bool) ∪ {true} = Set.univ := by
    ext b
    fin_cases b <;> simp
  have hMeasureUnion :
      (μ : Measure Bool) (({false} : Set Bool) ∪ {true}) =
        (μ : Measure Bool) {false} + (μ : Measure Bool) {true} :=
    measure_union (by simp) (measurableSet_singleton true)
  calc
    (μ : Measure Bool) {false} + (μ : Measure Bool) {true} =
        (μ : Measure Bool) (({false} : Set Bool) ∪ {true}) :=
      hMeasureUnion.symm
    _ = (μ : Measure Bool) Set.univ := by rw [hUnion]
    _ = 1 := by simp

/-- On the two-point Boolean carrier, vanishing of one atom forces the
probability measure to be the Dirac mass at the other point. -/
theorem probabilityMeasure_bool_eq_dirac_other_of_singleton_eq_zero
    (μ : ProbabilityMeasure Bool)
    (b : Bool)
    (hZero : (μ : Measure Bool) {b} = 0) :
    (μ : Measure Bool) = Measure.dirac (!b) := by
  fin_cases b
  · have hTrue : (μ : Measure Bool) {true} = 1 := by
      have hSum := probabilityMeasure_bool_singleton_sum μ
      simpa [hZero] using hSum
    apply Measure.ext_of_singleton
    intro x
    fin_cases x <;> simp [hZero, hTrue]
  · have hFalse : (μ : Measure Bool) {false} = 1 := by
      have hSum := probabilityMeasure_bool_singleton_sum μ
      simpa [hZero] using hSum
    apply Measure.ext_of_singleton
    intro x
    fin_cases x <;> simp [hZero, hFalse]

/-- A non-Dirac probability measure on `Bool` assigns strictly positive mass to
each of its two atoms. -/
theorem probabilityMeasure_bool_singleton_pos_of_ne_dirac
    (μ : ProbabilityMeasure Bool)
    (hNonDirac : ∀ b : Bool, (μ : Measure Bool) ≠ Measure.dirac b)
    (b : Bool) :
    0 < (μ : Measure Bool) {b} := by
  rw [pos_iff_ne_zero]
  intro hZero
  exact hNonDirac (!b)
    (probabilityMeasure_bool_eq_dirac_other_of_singleton_eq_zero μ b hZero)

/-- The automatically extracted continuum law, viewed on its canonical concrete
Boolean carrier. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBoolContinuumMeasure
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    ProbabilityMeasure Bool := by
  change ProbabilityMeasure Bool
  exact D.prokhorovSubsequenceLimit.continuumMeasure

/-- The concrete Boolean presentation of the automatically extracted continuum
law remains non-Dirac. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBoolContinuumMeasure_ne_dirac
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (b : Bool) :
    (D.prokhorovBoolContinuumMeasure : Measure Bool) ≠ Measure.dirac b := by
  let b' : D.prokhorovWeakLimit.Configuration := by
    change Bool
    exact b
  simpa [Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBoolContinuumMeasure,
    b'] using D.prokhorovContinuumMeasure_ne_dirac b'

/-- Both Boolean atoms of the automatically extracted continuum plaquette law
have strictly positive probability. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBoolContinuumMeasure_singleton_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (b : Bool) :
    0 < (D.prokhorovBoolContinuumMeasure : Measure Bool) {b} :=
  probabilityMeasure_bool_singleton_pos_of_ne_dirac
    D.prokhorovBoolContinuumMeasure
    D.prokhorovBoolContinuumMeasure_ne_dirac b

/-- In particular, the false plaquette-energy atom has positive continuum
probability. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovFalseAtom_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    0 < (D.prokhorovBoolContinuumMeasure : Measure Bool) {false} :=
  D.prokhorovBoolContinuumMeasure_singleton_pos false

/-- Likewise, the true plaquette-energy atom has positive continuum
probability. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovTrueAtom_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    0 < (D.prokhorovBoolContinuumMeasure : Measure Bool) {true} :=
  D.prokhorovBoolContinuumMeasure_singleton_pos true

/-- Since every Boolean singleton has positive mass, the automatically extracted
continuum plaquette law has full topological support. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBoolContinuumMeasure_support_eq_univ
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    (D.prokhorovBoolContinuumMeasure : Measure Bool).support = Set.univ := by
  ext b
  simp only [Set.mem_univ, iff_true]
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hbU : b ∈ U := mem_of_mem_nhds hU
  exact lt_of_lt_of_le
    (D.prokhorovBoolContinuumMeasure_singleton_pos b)
    (measure_mono (Set.singleton_subset_iff.mpr hbU))

end

end MathlibAnalytic
end MGAP4D
