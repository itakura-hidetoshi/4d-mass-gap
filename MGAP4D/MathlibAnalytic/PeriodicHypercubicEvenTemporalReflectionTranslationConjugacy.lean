import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIntegerTemporalTranslation
import Mathlib.Tactic

/-!
# Temporal reflection--translation conjugacy on the actual finite Wilson lattice

The continuum OS inner product contains correlations across the reflection plane, so positive-half
marginal stationarity alone is not sufficient for translating OS classes.  The required geometric
input is already present at finite Wilson scale: site reflection reverses every integer temporal
displacement.

This file proves that fact first on vertices, then on orientation-corrected physical positive links,
and finally on full finite configurations:

`θ (T_k A) = T_{-k} (θ A)`.

The configuration theorem uses only the existing pullback translation and the concrete physical
edge reflection.  No measure statement, continuum premise, OS contraction, null-space preservation,
semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Site reflection reverses an arbitrary integer temporal displacement. -/
theorem periodicHypercubicEvenTimeReflection_add_integerTemporalDisplacement
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    (k : ℤ) :
    periodicHypercubicEvenTimeReflection H
        (v + periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) k) =
      periodicHypercubicEvenTimeReflection H v +
        periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (-k) := by
  funext mu
  by_cases hmu : mu = (0 : Fin 4)
  · subst mu
    simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicIntegerTemporalDisplacement]
  · simp [periodicHypercubicEvenTimeReflection,
      periodicHypercubicIntegerTemporalDisplacement, hmu]

/-- Orientation-corrected positive-link reflection conjugates an integer temporal edge translation
to the opposite translation. -/
theorem periodicHypercubicEvenEdgeReflection_integerTemporalTranslation
    (H : ℕ)
    (k : ℤ)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenEdgeReflection H
        (periodicHypercubicEdgeTranslationEquiv
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicIntegerTemporalDisplacement
            (PeriodicHypercubicEvenSideLength H) k) e) =
      periodicHypercubicEdgeTranslationEquiv
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicIntegerTemporalDisplacement
          (PeriodicHypercubicEvenSideLength H) (-k))
        (periodicHypercubicEvenEdgeReflection H e) := by
  rcases e with ⟨v, mu⟩
  by_cases hmu : mu = (0 : Fin 4)
  · subst mu
    apply Prod.ext
    · simp only [periodicHypercubicEdgeTranslationEquiv_apply,
        periodicHypercubicEvenEdgeReflection_time, Prod.fst, Prod.snd]
      change
        periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenTimeReflection H
              (v + periodicHypercubicIntegerTemporalDisplacement
                (PeriodicHypercubicEvenSideLength H) k)) 0 =
          periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenTimeReflection H v) 0 +
            periodicHypercubicIntegerTemporalDisplacement
              (PeriodicHypercubicEvenSideLength H) (-k)
      rw [periodicHypercubicEvenTimeReflection_add_integerTemporalDisplacement]
      unfold periodicHypercubicUnshift
      abel
    · rfl
  · apply Prod.ext
    · simp only [periodicHypercubicEdgeTranslationEquiv_apply, Prod.fst, Prod.snd]
      rw [periodicHypercubicEvenEdgeReflection_spatial H _ hmu]
      rw [periodicHypercubicEvenEdgeReflection_spatial H _ hmu]
      exact periodicHypercubicEvenTimeReflection_add_integerTemporalDisplacement H v k
    · rfl

/-- Pointwise form of the integer temporal configuration pullback: evaluating `T_k A` at an
untranslated edge is the same as evaluating `A` at that edge translated by `-k`. -/
@[simp]
theorem periodicHypercubicIntegerTemporalConfigurationTranslation_apply
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ)
    (k : ℤ)
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicIntegerTemporalConfigurationTranslation n k A e =
      A
        (periodicHypercubicEdgeTranslationEquiv n
          (periodicHypercubicIntegerTemporalDisplacement n (-k)) e) := by
  have h :=
    periodicHypercubicIntegerTemporalConfigurationTranslation_apply_translatedEdge
      n k A
      (periodicHypercubicEdgeTranslationEquiv n
        (periodicHypercubicIntegerTemporalDisplacement n (-k)) e)
  rw [← periodicHypercubicIntegerTemporalEdgeTranslation_add_apply] at h
  simpa using h

/-- Concrete finite configuration reflection conjugates every integer temporal translation to its
inverse translation. -/
theorem periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation
    {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (H : ℕ)
    (k : ℤ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenConfigurationReflection H
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) k A) =
      periodicHypercubicIntegerTemporalConfigurationTranslation
        (PeriodicHypercubicEvenSideLength H) (-k)
        (periodicHypercubicEvenConfigurationReflection H A) := by
  funext e
  by_cases htime : e.2 = (0 : Fin 4)
  · simp [periodicHypercubicEvenConfigurationReflection, htime,
      periodicHypercubicEvenEdgeReflection_integerTemporalTranslation]
  · simp [periodicHypercubicEvenConfigurationReflection, htime,
      periodicHypercubicEvenEdgeReflection_integerTemporalTranslation]

end

end MathlibAnalytic
end MGAP4D
