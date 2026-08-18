import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalPathReflectionCompletion
import Mathlib.Tactic

/-!
# Intrinsic finite Wilson OS form on the reflection-completed primary rational path

The preceding layers provide two complementary facts from the same actual finite
Wilson source:

* finite reflection positivity for every bounded measurable cylinder supported
  on nonnegative primary rational-time slots; and
* an exact reflection completion whose source reflection is literally intrinsic
  path reflection `x(q) ↦ x(-q)`.

This file composes those facts.  The resulting quadratic form is written only in
terms of a reflection-completed rational path and its intrinsic path reflection,
while the integration source remains the actual finite Wilson Gibbs measure.
The pushforward to a path-space measure is deliberately left to the next layer.

No reflection-positivity premise, continuum premise, cross-scale raw-edge
identification, half-extent growth premise, physical-volume identity, `sorry`,
`admit`, or `axiom` is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance primaryIntrinsicOSTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryIntrinsicOSCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryIntrinsicOSSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryIntrinsicOSMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryIntrinsicOSBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Actual finite Wilson Osterwalder--Schrader positivity written intrinsically
on the reflection-completed primary rational path.

For every bounded measurable cylinder supported on finitely many nonnegative
rational times, the Wilson-source quadratic form is

`∫ F(X(A)) * F(Θ X(A)) dμ_W(A) ≥ 0`,

where `X` is the reflection-completed primary path and `Θ x(q) = x(-q)` is the
intrinsic rational path reflection.  No source-reflection expression remains in
the integrand. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathCylinder_wilsonSource_intrinsicReflectionPositive_boundedMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n J)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u, ‖g u‖ ≤ M) :
    0 ≤ ∫ A,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          H J g
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) *
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          H J g
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n A))
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have hJ : ∀ q : J, (0 : ℚ) ≤ q.1 := hslots.nonnegative
  have hsource :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_wilsonSource_reflectionPositive_boundedMeasurable
      H N hN beta hbeta latticeSpacing n J hslots g hg M hM hbound
  calc
    0 ≤ ∫ A,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
            H J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
              H latticeSpacing n A) *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
            H J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
              H latticeSpacing n
              (periodicHypercubicEvenConfigurationReflection H A))
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      hsource
    _ = ∫ A,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
            H J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n A) *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
            H J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
                H latticeSpacing n A))
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_readout
          H latticeSpacing n J g A,
        ← periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_reflectionCompleted_eq_rationalCylinder
          H latticeSpacing n J g A hJ,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_readout
          H latticeSpacing n J g
          (periodicHypercubicEvenConfigurationReflection H A),
        ← periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_reflectionCompleted_eq_rationalCylinder
          H latticeSpacing n J g
          (periodicHypercubicEvenConfigurationReflection H A) hJ,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection
          H latticeSpacing n A]

end

end MathlibAnalytic
end MGAP4D
