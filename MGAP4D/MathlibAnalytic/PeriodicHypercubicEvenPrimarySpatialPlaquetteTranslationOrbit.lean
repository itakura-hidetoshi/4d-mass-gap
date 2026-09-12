import MGAP4D.MathlibAnalytic.PeriodicHypercubicTranslationInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquettePathLaw
import Mathlib.Tactic

/-!
# Spatial translation orbit of the canonical primary scalar plaquette

The current same-root scalar continuum process is built from one canonical spatial plaquette on the
reflection-fixed time-zero slice.  A physical scalar glueball channel requires more than being
real-valued: before any `0⁺⁺` claim one must at least construct the spatial translation orbit used
for zero-momentum projection, and later add cubic/parity/charge-conjugation receipts.

This file performs only the first exact finite-Wilson step.  It

* defines periodic displacements with zero Euclidean-time component;
* translates the canonical `(1,2)` primary spatial plaquette by such displacements;
* proves that every translated plaquette remains on the time-zero slice with the same two spatial
  axes;
* defines its normalized-real-trace Wilson observable; and
* proves exact covariance with configuration translation, including exact readback to the already
  canonical primary-boundary scalar observable.

Thus the family is theorem-generated from the same actual Wilson configuration.  No zero-momentum
sum, cubic `A₁⁺⁺` projection, continuum spin identification, glueball mass, spectral statement, or
new physical assumption is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Periodic displacements tangent to the reflection-fixed time-zero spatial slice. -/
abbrev PeriodicHypercubicEvenSpatialDisplacement (H : ℕ) : Type :=
  {a : PeriodicHypercubicEvenVertex H // a 0 = 0}

/-- The zero spatial displacement. -/
def periodicHypercubicEvenZeroSpatialDisplacement
    (H : ℕ) : PeriodicHypercubicEvenSpatialDisplacement H :=
  ⟨0, by simp⟩

/-- Translate the canonical primary `(1,2)` spatial plaquette inside the time-zero slice. -/
def periodicHypercubicEvenPrimarySpatialPlaquetteTranslate
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    PeriodicHypercubicEvenPlaquette H :=
  periodicHypercubicPlaquetteTranslationEquiv
    (PeriodicHypercubicEvenSideLength H) a.1
    (periodicHypercubicEvenPrimarySpatialPlaquette H)

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_base
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a).1 = a.1 := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteTranslate,
    periodicHypercubicEvenPrimarySpatialPlaquette]

/-- Every translated primary plaquette still has time coordinate zero. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_base_time
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a).1 0 = 0 := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_base]
  exact a.2

/-- Spatial translation does not change the first plaquette axis. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_firstAxis
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteFirstAxis
        (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a) =
      (1 : PeriodicHypercubicAxis) := by
  rfl

/-- Spatial translation does not change the second plaquette axis. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_secondAxis
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteSecondAxis
        (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a) =
      (2 : PeriodicHypercubicAxis) := by
  rfl

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_zero
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H
        (periodicHypercubicEvenZeroSpatialDisplacement H) =
      periodicHypercubicEvenPrimarySpatialPlaquette H := by
  rfl

/-- Normalized real trace of a translated canonical primary spatial plaquette.  This is the finite
same-root observable family from which a later zero-spatial-momentum projection can be formed. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  normalizedSpecialUnitaryRealTrace N
    (periodicHypercubicPlaquetteHolonomy A
      (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a))

/-- Package all spatial translates as one finite-volume observable family. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceOrbit
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpatialDisplacement H → ℝ :=
  fun a =>
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N a A

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace_zero
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N
        (periodicHypercubicEvenZeroSpatialDisplacement H) A =
      normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  rfl

local instance primarySpatialOrbitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Simultaneously translating the configuration and the primary plaquette gives exactly the
untranslated primary normalized trace. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace_configurationTranslation
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N a
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) a.1 A) =
      normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace
  exact congrArg (normalizedSpecialUnitaryRealTrace N)
    (periodicHypercubicPlaquetteHolonomy_configurationTranslation
      a.1 A (periodicHypercubicEvenPrimarySpatialPlaquette H))

/-- Audit-visible bridge back to the exact primary-boundary scalar coordinate already used by the
same-root rational path construction. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace_configurationTranslation_eq_primaryBoundary
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N a
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) a.1 A) =
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary H N
        (fun e => A e.1) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace_configurationTranslation,
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_restrict_eq_actual]

end

end MathlibAnalytic
end MGAP4D
