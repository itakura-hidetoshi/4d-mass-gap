import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquettePathLaw
import Mathlib.Tactic

/-!
# Intrinsic finite OS positivity on the canonical scalar rational path law

The preceding layer pushes the reflection-completed one-sided primary edge path
to the fixed scalar carrier `ℚ → ℝ` using the normalized trace of the canonical
primary spatial plaquette.  This file transports the already-proved intrinsic
edge-path Osterwalder--Schrader inequality through that scalarization.

For every bounded measurable cylinder on finitely many admissible nonnegative
rational slots we obtain directly on the scalar path law

`0 ≤ ∫ x, F(x) * F(Θ x) ∂ μ_scalar`.

No reflection-positivity premise, cross-scale equality, continuum premise,
positive-time closedness premise, or new physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance primaryScalarOSPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryScalarOSPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryScalarOSPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryScalarOSPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryScalarOSPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Finite restriction of a scalar rational path. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathFiniteRestriction
    (J : Finset ℚ)
    (x : ℚ → ℝ) :
    ∀ q : J, ℝ :=
  fun q => x q.1

/-- Finite scalar rational-slot restriction is measurable. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathFiniteRestriction_measurable
    (J : Finset ℚ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathFiniteRestriction J) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_pi_apply q.1

/-- A bounded-measurable test cylinder on the fixed scalar rational path. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (x : ℚ → ℝ) : ℝ :=
  g (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathFiniteRestriction J x)

/-- Measurability of scalar path cylinders. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder_measurable
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder J g) :=
  hg.comp
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathFiniteRestriction_measurable J)

/-- Lift a scalar finite-slot cylinder back to the edge-valued finite-slot
carrier by applying the canonical primary-plaquette trace in each slot. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
    (H N : ℕ)
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (u :
      ∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  g (fun q =>
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
      H N (u q))

/-- The finite-slot scalarization used by the lifted cylinder is measurable. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteFiniteSlotMap_measurable
    (H N : ℕ)
    (J : Finset ℚ) :
    Measurable
      (fun u :
          (∀ q : J,
            PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        fun q : J =>
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary
            H N (u q)) := by
  apply measurable_pi_lambda
  intro q
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_measurable
      H N).comp (measurable_pi_apply q)

/-- Measurability of the edge-valued lift of a scalar cylinder. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder_measurable
    (H N : ℕ)
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
        H N J g) :=
  hg.comp
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteFiniteSlotMap_measurable
      H N J)

/-- The lifted edge cylinder has exactly the same uniform bound as the scalar
cylinder. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder_bound
    (H N : ℕ)
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (M : ℝ)
    (hbound : ∀ v, ‖g v‖ ≤ M) :
    ∀ u,
      ‖periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
        H N J g u‖ ≤ M := by
  intro u
  exact hbound _

/-- Evaluating the lifted edge cylinder is definitionally the same as first
scalarizing the full edge path and then evaluating the scalar cylinder. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_scalarPlaquetteLift_eq
    (H N : ℕ)
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (x : ℚ →
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
          H N J g) x =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
        J g
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N x) := by
  rfl

/-- The reflected lifted edge cylinder is exactly the scalar cylinder evaluated
on the intrinsic scalar reflection. -/
@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_scalarPlaquetteLift_reflection_eq
    (H N : ℕ)
    (J : Finset ℚ)
    (g : (∀ q : J, ℝ) → ℝ)
    (x : ℚ →
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
        H J
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
          H N J g)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H x) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
        J g
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
            H N x)) := by
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_scalarPlaquetteLift_eq]
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_reflection]

/-- Actual finite Osterwalder--Schrader reflection positivity on the fixed
canonical scalar plaquette rational path law.

The only slot condition is the same finite nonnegative physical-floor
admissibility already used by the one-sided primary Wilson theorem. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_intrinsicReflectionPositive_boundedMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n J)
    (g : (∀ q : J, ℝ) → ℝ)
    (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ v, ‖g v‖ ≤ M) :
    0 ≤ ∫ x,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
          J g x *
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
          J g
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x)
      ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n := by
  let gEdge :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
      H N J g
  have hgEdge : Measurable gEdge := by
    dsimp [gEdge]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder_measurable
        H N J g hg
  have hboundEdge : ∀ u, ‖gEdge u‖ ≤ M := by
    dsimp [gEdge]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder_bound
        H N J g M hbound
  have hedge :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure_intrinsicReflectionPositive_boundedMeasurable
      H N hN beta hbeta latticeSpacing n J hslots gEdge hgEdge M hM hboundEdge
  have hedgeScalar :
      0 ≤ ∫ x,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
            J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
              H N x) *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
            J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
                H N x))
        ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
          H N hN beta hbeta latticeSpacing n := by
    simpa only [gEdge,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_scalarPlaquetteLift_eq,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_scalarPlaquetteLift_reflection_eq]
      using hedge
  have hScalarize :
      Measurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
      H N
  have hCylinder :
      Measurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
          J g) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder_measurable
      J g hg
  have hTheta :
      Measurable
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable
  have hIntegrand :
      Measurable
        (fun x : ℚ → ℝ =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
              J g x *
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
              J g
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x)) :=
    hCylinder.mul (hCylinder.comp hTheta)
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
  have hmap :
      (∫ x,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
            J g x *
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
            J g
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x)
        ∂Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
            H N hN beta hbeta latticeSpacing n)) =
        ∫ x,
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
              J g
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
                H N x) *
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathCylinder
              J g
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
                  H N x))
          ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
            H N hN beta hbeta latticeSpacing n := by
    exact MeasureTheory.integral_map
      hScalarize.aemeasurable hIntegrand.aestronglyMeasurable
  rw [hmap]
  exact hedgeScalar

end

end MathlibAnalytic
end MGAP4D
