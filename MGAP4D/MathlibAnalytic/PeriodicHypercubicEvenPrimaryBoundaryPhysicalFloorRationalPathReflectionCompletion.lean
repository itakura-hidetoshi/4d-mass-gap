import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalPathCylinderWilsonExpectation
import Mathlib.Tactic

/-!
# Reflection completion of the one-sided primary rational path

The one-sided primary rational path constructed previously is the correct
positive-time object for finite Wilson OS positivity, but its raw edge-valued
carrier was intentionally not declared reflection covariant.  This file adds a
finite-scale reflection completion without identifying carriers across scales.

For nonnegative rational time we keep the existing primary readout.  For a
negative rational time `q`, we read the positive time `-q` from the reflected
finite Wilson configuration.  The only gluing point is `q = 0`; there the
primary spatial slice is fixed pointwise by the finite configuration
reflection.  Consequently source reflection becomes exactly intrinsic path
reflection on the completed path.

No floor-sign identity, cross-scale raw-edge identification, continuum premise,
reflection-positivity premise, half-extent growth premise, physical-volume
identity, `sorry`, `admit`, or `axiom` is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A vertex underlying a primary spatial boundary edge is fixed by Euclidean
time reflection. -/
theorem periodicHypercubicEvenTimeReflection_primarySpatialBoundaryVertex
    (H : ℕ)
    (e : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H) :
    periodicHypercubicEvenTimeReflection H e.1.1 = e.1.1 := by
  funext i
  by_cases hi : i = 0
  · subst i
    have ht : e.1.1 0 = 0 := (ZMod.val_eq_zero _).mp e.2.2
    simp [periodicHypercubicEvenTimeReflection, ht]
  · simp [periodicHypercubicEvenTimeReflection, hi]

/-- Every primary spatial boundary edge is fixed pointwise by the oriented edge
reflection. -/
theorem periodicHypercubicEvenEdgeReflection_primarySpatialBoundary
    (H : ℕ)
    (e : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H) :
    periodicHypercubicEvenEdgeReflection H e.1 = e.1 := by
  rw [periodicHypercubicEvenEdgeReflection_spatial H e.1 e.2.1]
  apply Prod.ext
  · exact
      periodicHypercubicEvenTimeReflection_primarySpatialBoundaryVertex H e
  · rfl

/-- Configuration reflection fixes every primary spatial boundary link value. -/
@[simp]
theorem periodicHypercubicEvenConfigurationReflection_primarySpatialBoundary
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (e : PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H) :
    periodicHypercubicEvenConfigurationReflection H A e.1 = A e.1 := by
  rw [periodicHypercubicEvenConfigurationReflection_spatial H A e.1 e.2.1]
  rw [periodicHypercubicEvenEdgeReflection_primarySpatialBoundary H e]

/-- The time-zero primary spatial readout is fixed by configuration reflection. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_zero_configurationReflection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H 0
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H 0 A := by
  funext e
  simp [periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime]

/-- The rational physical-floor primary path at `q = 0` is reflection fixed. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_zero_configurationReflection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) 0 =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A 0 := by
  simpa [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout,
      physicalTemporalFloorStep] using
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_zero_configurationReflection
      H A

/-- Intrinsic rational-time reflection on the finite-scale primary path carrier. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
    {Gauge : Type*}
    (H : ℕ)
    (x : ℚ → (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge)) :
    ℚ → (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) :=
  fun q => x (-q)

/-- Rational path reflection is an involution. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection_involutive
    {Gauge : Type*}
    (H : ℕ) :
    Function.Involutive
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
        (Gauge := Gauge) H) := by
  intro x
  funext q
  simp [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection]

/-- Reflection-completed finite-scale primary path.  Positive times use the
original one-sided readout; negative times use the reflected source at the
corresponding positive time. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    ℚ → (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) :=
  fun q =>
    if 0 ≤ q then
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A q
    else
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) (-q)

/-- On nonnegative rational times the reflection completion is literally the
original primary rational path. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (q : ℚ)
    (hq : 0 ≤ q) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A q =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A q := by
  simp [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
    hq]

/-- On strictly negative rational times the reflection completion reads the
reflected source at the corresponding positive time. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_negative
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (q : ℚ)
    (hq : q < 0) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A q =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) (-q) := by
  simp [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
    not_le.mpr hq]

/-- Exact covariance: reflecting the finite Wilson source is the same as
intrinsically reflecting the reflection-completed rational path. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) := by
  funext q
  by_cases hzero : q = 0
  · subst q
    simp [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection]
  · by_cases hq : 0 ≤ q
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
      have hneg : ¬ 0 ≤ -q := by linarith
      simp [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection,
        hq, hneg]
    · have hqneg : q < 0 := lt_of_not_ge hq
      have hnonneg : 0 ≤ -q := by linarith
      simp only [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection,
        if_neg hq, if_pos hnonneg]
      rw [periodicHypercubicEvenConfigurationReflection_involutive H A]

/-- Restricting a reflection-completed path to nonnegative slots recovers the
same finite joint readout used by the Wilson OS theorem. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_reflectionCompleted_eq_readout
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
        H J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J A := by
  calc
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
        H J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
        H J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          H latticeSpacing n A) := by
      funext q
      exact
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
          H latticeSpacing n A q.1 (hJ q)
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J A :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_readout
        H latticeSpacing n J A

/-- Every nonnegative finite path cylinder evaluates on the reflection-completed
path exactly as the finite rational Wilson cylinder already used in #1791. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_reflectionCompleted_eq_rationalCylinder
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J g
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g A := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_reflectionCompleted_eq_readout
      H latticeSpacing n J A hJ]
  rfl

end

end MathlibAnalytic
end MGAP4D
