import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundarySpatialCylinderReflectionPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedFloorTemporalApproximation
import Mathlib.Tactic

/-!
# Finite positive rational-time primary-boundary cylinders and Wilson OS positivity

The preceding one-sided primary-boundary theorem gives actual finite Wilson
Osterwalder--Schrader positivity at one integer time `k <= H`.  This file
packages the finitely many rational physical times that occur in a cylinder
observable without adding any global relation between the half extent and the
lattice spacing.

For a finite set `J : Finset ℚ`, each rational slot is assigned its canonical
physical floor step and converted to a natural time index.  Admissibility records
exactly the two finite-scale facts needed by a positive-time cylinder:

* every rational slot is nonnegative; and
* every selected natural floor step lies in the primary positive half,
  `Int.toNat (physicalTemporalFloorStep ...) <= H`.

Under that explicit finite-scale receipt, the joint primary spatial readout is
independent of the negative open-half coordinate.  Hence every bounded measurable
scalar cylinder of all slots has a measurable boundary-positive representative,
and the actual finite Wilson Gibbs measure satisfies the corresponding OS
inequality.

No eventual half-extent growth, physical-volume identity, reflection-positivity
premise, continuum premise, or cross-scale coherence premise is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Finite-scale admissibility for a finite set of positive rational physical
slots.  The second field is deliberately local to the current lattice scale;
no eventual statement such as `H_n a_n -> ∞` is hidden here. -/
structure PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) : Prop where
  nonnegative : ∀ q : J, (0 : ℚ) ≤ q.1
  withinHalfExtent : ∀ q : J,
    Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q.1 : ℚ) : ℝ) n) ≤ H

/-- Joint readout of all primary spatial boundary data at finitely many rational
physical floor times.  Every coordinate is read directly from the same actual
finite configuration. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    ∀ q : J, PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge :=
  fun q =>
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q.1 : ℚ) : ℝ) n)) A

/-- The finite rational joint readout is measurable into the finite product of
primary spatial boundary configuration spaces. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        (Gauge := Gauge) H latticeSpacing n J) := by
  apply measurable_pi_lambda
  intro q
  simpa [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout] using
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_measurable
      (Gauge := Gauge) H
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q.1 : ℚ) : ℝ) n)))

/-- If all rational floor slots are within the primary half extent, changing the
negative open-half coordinate cannot change the entire joint rational readout. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_boundaryFibered_independent_negative
    {H : ℕ} {Value : Type*}
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n J)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y₁ y₂ :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  funext q
  simpa [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout] using
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_boundaryFibered_independent_negative
      (H := H)
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q.1 : ℚ) : ℝ) n))
      (hslots.withinHalfExtent q) b x y₁ y₂)

/-- A scalar cylinder depending on all selected positive rational physical
slots of the one-sided primary spatial readout. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : ℝ :=
  g (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
    H latticeSpacing n J A)

/-- Measurability of a scalar finite rational cylinder follows by composition
with the joint measurable readout. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g) := by
  exact hg.comp
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_measurable
      (Gauge := Gauge) H latticeSpacing n J)

/-- Every admissible finite rational cylinder is negative-half independent in
canonical boundary-fibered coordinates. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder_boundaryFibered_independent_negative
    {H : ℕ} {Value : Type*}
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n J)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Value) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y₁ y₂ :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  exact congrArg g
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_boundaryFibered_independent_negative
      latticeSpacing n J hslots b x y₁ y₂)

local instance primaryRationalCylinderTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryRationalCylinderCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryRationalCylinderSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryRationalCylinderMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryRationalCylinderBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Boundary-positive representative of an admissible finite rational cylinder.
The dummy negative coordinate is fixed to the identity. -/
noncomputable def periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) : ℝ :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
    H latticeSpacing n J g
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      z.1 z.2 (fun _ => 1))

/-- The boundary-positive rational-cylinder representative is measurable. -/
theorem periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_measurable
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
        H N latticeSpacing n J g) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let embed :
      P.BoundaryConfiguration Gauge × P.OpenHalfConfiguration Gauge →
        P.BoundaryConfiguration Gauge ×
          (P.OpenHalfConfiguration Gauge × P.OpenHalfConfiguration Gauge) :=
    fun z => (z.1, (z.2, fun _ => 1))
  have hembed : Continuous embed := by
    exact continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have hassemble : Measurable
      (fun z : P.BoundaryConfiguration Gauge × P.OpenHalfConfiguration Gauge =>
        P.boundaryFiberedAssemble z.1 z.2 (fun _ => 1)) := by
    have h := (P.continuous_boundaryFiberedAssemble Gauge).comp hembed
    simpa [embed, Function.comp_def] using h.measurable
  have hcylinder : Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        (Gauge := Gauge) H latticeSpacing n J g) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder_measurable
      H latticeSpacing n J g hg
  exact hcylinder.comp hassemble

/-- A uniform bound on the scalar rational cylinder is inherited verbatim by
its boundary-positive representative. -/
theorem periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_norm_le
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (M : ℝ)
    (hbound : ∀ u, ‖g u‖ ≤ M)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
        H N latticeSpacing n J g z‖ ≤ M := by
  exact hbound _

/-- On admissible slots, the canonical boundary/positive restriction of a full
configuration reconstructs the original joint rational cylinder exactly. -/
theorem periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_reconstruct
    (H N : ℕ)
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
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
        H N latticeSpacing n J g
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
          (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g A := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let F : (PeriodicHypercubicEvenEdge H → Gauge) → ℝ :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
      H latticeSpacing n J g
  have hlocal :
      F (P.boundaryFiberedAssemble
          (P.boundaryRestriction A) (P.positiveRestriction A) (fun _ => 1)) =
        F (P.boundaryFiberedAssemble
          (P.boundaryRestriction A) (P.positiveRestriction A)
          (P.negativeRestriction A)) := by
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder_boundaryFibered_independent_negative
        latticeSpacing n J hslots g
        (P.boundaryRestriction A) (P.positiveRestriction A)
        (fun _ => 1) (P.negativeRestriction A)
  have hcoord :
      F (P.boundaryFiberedAssemble
          (P.boundaryRestriction A) (P.positiveRestriction A)
          (P.negativeRestriction A)) = F A :=
    congrArg F ((P.boundaryFiberedCoordinates Gauge).left_inv A)
  calc
    periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
        H N latticeSpacing n J g
        (P.boundaryRestriction A, P.positiveRestriction A) =
      F (P.boundaryFiberedAssemble
        (P.boundaryRestriction A) (P.positiveRestriction A) (fun _ => 1)) := rfl
    _ = F (P.boundaryFiberedAssemble
        (P.boundaryRestriction A) (P.positiveRestriction A)
        (P.negativeRestriction A)) := hlocal
    _ = F A := hcoord
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
        H latticeSpacing n J g A := rfl

/-- Actual finite Wilson Osterwalder--Schrader positivity for every bounded
measurable cylinder of finitely many admissible positive rational physical floor
slots of the primary spatial boundary.

This is the finite positive-rational-cylinder statement needed before passing to
a same-root rational path law.  The only half-extent input is the explicit
finite-scale slot admissibility above. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder_wilsonGibbs_reflectionPositive_boundedMeasurable
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
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
          H latticeSpacing n J g A *
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
          H latticeSpacing n J g
          (periodicHypercubicEvenConfigurationReflection H A)
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have hpos :=
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedMeasurable
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
        H N latticeSpacing n J g)
      (periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_measurable
        H N latticeSpacing n J g hg)
      M hM
      (fun z =>
        periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_norm_le
          H N latticeSpacing n J g M hbound z)
  calc
    0 ≤ ∫ A,
        periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H
          (periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
            H N latticeSpacing n J g) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      hpos
    _ = ∫ A,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
            H latticeSpacing n J g A *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
            H latticeSpacing n J g
            (periodicHypercubicEvenConfigurationReflection H A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      simp only [periodicHypercubicEvenBoundaryPositiveFullReflectedObservable]
      rw [
        periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_reconstruct
          H N latticeSpacing n J hslots g A,
        periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_reconstruct
          H N latticeSpacing n J hslots g
          (periodicHypercubicEvenConfigurationReflection H A)]

end

end MathlibAnalytic
end MGAP4D
