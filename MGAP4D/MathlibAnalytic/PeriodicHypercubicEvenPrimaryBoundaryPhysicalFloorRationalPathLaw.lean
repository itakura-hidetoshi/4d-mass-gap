import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalCylinderReflectionPositivity
import Mathlib.Tactic

/-!
# Same-root primary-boundary rational path law

The finite positive-rational-cylinder theorem already reads every selected slot
from one actual finite Wilson configuration.  This file packages the same
one-sided readout as a countable rational path and pushes the actual Wilson Gibbs
measure forward along it.

The carrier is intentionally finite-scale and may depend on `H`.  This file does
not claim a cross-scale continuum carrier.  Its role is to make the same-root
path law and all finite cylinder marginals exact before a later gauge-invariant
scalarization / reflection-completion step.

No reflection-positivity premise, continuum premise, half-extent growth premise,
physical-volume identity, or cross-scale coherence is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The entire rational physical-floor path of primary spatial boundary data at
one finite scale.  Every rational coordinate is read from the same actual full
configuration. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    ℚ → (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) :=
  fun q =>
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n)) A

/-- The full rational primary-spatial path readout is measurable into the
countable product measurable space. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        (Gauge := Gauge) H latticeSpacing n) := by
  apply measurable_pi_lambda
  intro q
  simpa [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout] using
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_measurable
      (Gauge := Gauge) H
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n)))

local instance primaryRationalPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryRationalPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryRationalPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryRationalPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryRationalPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The finite-scale rational path law obtained by direct pushforward of the
actual finite Wilson Gibbs measure. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measure
      (ℚ →
        (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  Measure.map
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      H latticeSpacing n)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure

/-- The normalized form of the same same-source rational path law. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    ProbabilityMeasure
      (ℚ →
        (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsProbabilityMeasure.map
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_measurable
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        H latticeSpacing n).aemeasurable

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n :
        Measure
          (ℚ →
            (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  rfl

/-- Audit-visible same-root identity: the full primary rational path is pushed
forward directly from the actual finite Wilson Gibbs measure. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure_eq_map_wilson
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  rfl

/-- Restrict a full rational primary-spatial path to a finite set of rational
slots. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
    {Gauge : Type*}
    (H : ℕ)
    (J : Finset ℚ)
    (x : ℚ → (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge)) :
    ∀ q : J, PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge :=
  fun q => x q.1

/-- Finite rational slot restriction is measurable. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (J : Finset ℚ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
        (Gauge := Gauge) H J) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_pi_apply q.1

/-- Restricting the full rational path readout to `J` is definitionally the
joint finite rational readout constructed for Wilson OS positivity. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_readout
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
        H J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          H latticeSpacing n A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J A := by
  rfl

/-- Every finite joint marginal of the primary rational path law is exactly the
pushforward of the same Wilson Gibbs measure by the finite joint readout from
#1791. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure_finiteRestriction_eq_map_wilson
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathMeasure
  calc
    Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H J)
        (Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      Measure.map
        ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H J) ∘
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      Measure.map_map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_measurable
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_measurable
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n)
    _ = Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      congr 1

/-- A scalar cylinder on the full primary rational path, supported on a finite
slot set `J`. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
    {Gauge : Type*}
    (H : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (x : ℚ → (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge)) : ℝ :=
  g (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction
    H J x)

/-- Measurability of a finite scalar path cylinder follows from finite slot
restriction. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J g) := by
  exact hg.comp
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathFiniteRestriction_measurable
      (Gauge := Gauge) H J)

/-- Evaluating a finite path cylinder on the actual path readout is exactly the
finite Wilson configuration cylinder from #1791. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_readout
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J g
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          H latticeSpacing n A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g A := by
  rfl

end

end MathlibAnalytic
end MGAP4D
