import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalReflectionCovariance
import Mathlib.Tactic

/-!
# Pointwise temporal reflection--translation receipts on the finite Wilson lattice

The canonical repository already contains the geometric theorems that site, positive-edge, and full
configuration reflection reverse integer temporal translations.  This file does not duplicate those
results.  It adds only the pointwise inverse-pullback formula for the existing configuration action
and a pointwise corollary of the already-proved configuration conjugacy.

These receipts are convenient for subsequent same-root primary-scalar OS calculations, where
translated and reflected finite observables are compared edge by edge.

No new reflection theorem, measure statement, continuum premise, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

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

/-- Pointwise corollary of the existing finite configuration reflection--translation conjugacy. -/
theorem periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation_apply
    {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (H : ℕ)
    (k : ℤ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenConfigurationReflection H
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) k A) e =
      periodicHypercubicIntegerTemporalConfigurationTranslation
        (PeriodicHypercubicEvenSideLength H) (-k)
        (periodicHypercubicEvenConfigurationReflection H A) e :=
  congrFun
    (periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation
      H k A) e

end

end MathlibAnalytic
end MGAP4D
