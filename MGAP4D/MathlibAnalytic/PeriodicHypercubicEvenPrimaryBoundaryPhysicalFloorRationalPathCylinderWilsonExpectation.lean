import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalPathLaw
import Mathlib.Tactic

/-!
# Same-root primary rational path-cylinder Wilson expectations

The finite-scale primary rational path law is already the direct pushforward of
the actual even-periodic Wilson Gibbs measure.  This file records the corresponding
expectation identity for arbitrary measurable finite path cylinders and rewrites
the finite positive-rational Wilson OS theorem from the same source entirely in
path-readout notation.

This is deliberately still a finite-scale statement.  In particular, it does not
identify the raw edge-valued carriers across different `H`, and it does not assert
that source reflection is already a path-space time-reflection operator.  That
covariance remains a separate geometric step.

No reflection-positivity premise, continuum premise, half-extent growth premise,
physical-volume identity, cross-scale coherence, `sorry`, `admit`, or `axiom` is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance primaryRationalPathExpectationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryRationalPathExpectationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryRationalPathExpectationSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryRationalPathExpectationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryRationalPathExpectationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Integrating a measurable finite cylinder against the primary rational path
law is exactly the same as integrating the corresponding finite rational
cylinder against the actual Wilson Gibbs source from which that path law was
pushed forward. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_integral_eq_wilson
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g) :
    (∫ x,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J g x
      ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n) =
      ∫ A,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
          H latticeSpacing n J g A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
  calc
    (∫ x,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J g x
      ∂Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ A,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          H J g
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      exact MeasureTheory.integral_map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_measurable
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n).aemeasurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_measurable
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H J g hg).aestronglyMeasurable
    _ = ∫ A,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
          H latticeSpacing n J g A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      rfl

/-- The finite Wilson OS inequality from the positive rational-cylinder theorem
can be stated directly using the complete primary rational path readout on the
same actual Wilson configuration and on its actual finite reflection.

This is not yet a path-space reflection theorem: both path factors are still
read from the common finite Wilson source. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_wilsonSource_reflectionPositive_boundedMeasurable
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
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n A) *
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          H J g
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n
            (periodicHypercubicEvenConfigurationReflection H A))
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  simpa using
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder_wilsonGibbs_reflectionPositive_boundedMeasurable
      H N hN beta hbeta latticeSpacing n J hslots g hg M hM hbound)

end

end MathlibAnalytic
end MGAP4D
