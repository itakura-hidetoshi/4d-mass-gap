import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialAxis1ReflectionGeometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedRealTraceConjugation
import Mathlib.Tactic

/-!
# Axis-`1` reflection invariance of the all-spatial zero-momentum plaquette operator

The preceding geometry layer constructs the independent spatial sign flip needed beyond ordinary
axis permutations.  For a plaquette in plane `(1,2)` or `(1,3)`, reflecting axis `1` reverses one
coordinate direction.  After rebasing the positive-link plaquette at `R₁(a) - e₁`, the transformed
holonomy is a cyclic rebase of the inverse original holonomy, hence a conjugate of that inverse.
For plane `(2,3)`, the reflected base is simply `R₁(a)` and the holonomy is unchanged exactly.

Normalized-real-trace invariance under inversion and conjugation therefore removes the orientation
change.  Reindexing the finite time-zero displacement carrier proves invariance of every plane
zero-momentum component and hence of the equal-weight all-spatial zero-momentum observable.

This supplies one independent sign-flip generator at the observable level.  Together with the two
adjacent axis swaps it is the generating data for finite signed spatial permutations, but this file
does not yet package or name a full cubic representation and makes no continuum-spin or spectral
claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

@[simp]
theorem periodicHypercubicEvenSpatialAxis1Reflection_self
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialAxis1Reflection H
        (periodicHypercubicEvenSpatialAxis1Reflection H v) = v :=
  periodicHypercubicEvenSpatialAxis1Reflection_involutive H v

/-- Plane-dependent base point used after reflecting axis `1`.
Planes containing axis `1` need one negative axis-`1` shift; plane `(2,3)` does not. -/
def periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    PeriodicHypercubicEvenSpatialDisplacement H :=
  match plane with
  | .plane12 =>
      ⟨periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialAxis1Reflection H a.1) 1,
        by
          simp [periodicHypercubicUnshift, periodicHypercubicUnit,
            periodicHypercubicEvenSpatialAxis1Reflection, a.2]⟩
  | .plane13 =>
      ⟨periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialAxis1Reflection H a.1) 1,
        by
          simp [periodicHypercubicUnshift, periodicHypercubicUnit,
            periodicHypercubicEvenSpatialAxis1Reflection, a.2]⟩
  | .plane23 =>
      ⟨periodicHypercubicEvenSpatialAxis1Reflection H a.1,
        by simp [periodicHypercubicEvenSpatialAxis1Reflection, a.2]⟩

@[simp]
theorem periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase_plane12
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H .plane12 a).1 =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H a.1) 1 :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase_plane13
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H .plane13 a).1 =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialAxis1Reflection H a.1) 1 :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase_plane23
    (H : ℕ) (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H .plane23 a).1 =
      periodicHypercubicEvenSpatialAxis1Reflection H a.1 :=
  rfl

/-- The plane-dependent axis-`1` reflection rebase is involutive. -/
theorem periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase_involutive
    (H : ℕ) (plane : PeriodicHypercubicSpatialPlane) :
    Function.Involutive
      (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H plane) := by
  intro a
  apply Subtype.ext
  cases plane with
  | plane12 =>
      change
        periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialAxis1Reflection H
              (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
                (periodicHypercubicEvenSpatialAxis1Reflection H a.1) 1)) 1 = a.1
      rw [periodicHypercubicEvenSpatialAxis1Reflection_unshift_axis1,
        periodicHypercubicEvenSpatialAxis1Reflection_self]
      exact periodicHypercubicUnshift_shift
        (PeriodicHypercubicEvenSideLength H) a.1 1
  | plane13 =>
      change
        periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialAxis1Reflection H
              (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
                (periodicHypercubicEvenSpatialAxis1Reflection H a.1) 1)) 1 = a.1
      rw [periodicHypercubicEvenSpatialAxis1Reflection_unshift_axis1,
        periodicHypercubicEvenSpatialAxis1Reflection_self]
      exact periodicHypercubicUnshift_shift
        (PeriodicHypercubicEvenSideLength H) a.1 1
  | plane23 =>
      exact periodicHypercubicEvenSpatialAxis1Reflection_self H a.1

/-- Axis-`1` reflection rebase as a finite-carrier equivalence for zero-momentum reindexing. -/
def periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebaseEquiv
    (H : ℕ) (plane : PeriodicHypercubicSpatialPlane) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun := periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H plane
  invFun := periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H plane
  left_inv := periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase_involutive H plane
  right_inv := periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase_involutive H plane

/-- Conjugating edge value for the cyclic rebase in a plane containing axis `1`. -/
def periodicHypercubicEvenSpatialAxis1ReflectionConjugator
    {H : ℕ} {Gauge : Type*} [Group Gauge]
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : Gauge :=
  (A (a.1, (1 : PeriodicHypercubicAxis)))⁻¹

/-- In plane `(1,2)`, axis-`1` reflection yields a conjugate of the inverse holonomy. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_axis1Reflection_plane12
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H .plane12 a)
          .plane12) =
      periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A *
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12))⁻¹ *
        (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A)⁻¹ := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    PeriodicHypercubicSpatialPlane.axisPair,
    periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase,
    periodicHypercubicEvenSpatialAxis1ReflectionConjugator,
    periodicHypercubicEvenConfigurationSpatialAxis1Reflection,
    periodicHypercubicEvenEdgeSpatialAxis1Reflection,
    periodicHypercubicEvenSpatialAxis1Reflection_shift_axis1,
    periodicHypercubicEvenSpatialAxis1Reflection_shift_other,
    periodicHypercubicEvenSpatialAxis1Reflection_unshift_axis1,
    periodicHypercubicEvenSpatialAxis1Reflection_unshift_other,
    periodicHypercubicEvenSpatialAxis1Reflection_self,
    periodicHypercubicShift_comm,
    periodicHypercubicUnshift_shift] <;>
  group

/-- In plane `(1,3)`, axis-`1` reflection yields a conjugate of the inverse holonomy. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_axis1Reflection_plane13
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H .plane13 a)
          .plane13) =
      periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A *
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13))⁻¹ *
        (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A)⁻¹ := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    PeriodicHypercubicSpatialPlane.axisPair,
    periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase,
    periodicHypercubicEvenSpatialAxis1ReflectionConjugator,
    periodicHypercubicEvenConfigurationSpatialAxis1Reflection,
    periodicHypercubicEvenEdgeSpatialAxis1Reflection,
    periodicHypercubicEvenSpatialAxis1Reflection_shift_axis1,
    periodicHypercubicEvenSpatialAxis1Reflection_shift_other,
    periodicHypercubicEvenSpatialAxis1Reflection_unshift_axis1,
    periodicHypercubicEvenSpatialAxis1Reflection_unshift_other,
    periodicHypercubicEvenSpatialAxis1Reflection_self,
    periodicHypercubicShift_comm,
    periodicHypercubicUnshift_shift] <;>
  group

/-- Plane `(2,3)` is unchanged exactly under reflection of axis `1`. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_axis1Reflection_plane23
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H .plane23 a)
          .plane23) =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane23) := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    PeriodicHypercubicSpatialPlane.axisPair,
    periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase,
    periodicHypercubicEvenConfigurationSpatialAxis1Reflection,
    periodicHypercubicEvenEdgeSpatialAxis1Reflection,
    periodicHypercubicEvenSpatialAxis1Reflection_shift_other,
    periodicHypercubicEvenSpatialAxis1Reflection_self]

/-- One translated spatial normalized-real-trace plaquette is invariant under the axis-`1`
reflection after its canonical plane-dependent rebase. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_axis1Reflection
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane
        (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebase H plane a)
        (periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A) =
      periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A := by
  cases plane with
  | plane12 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_axis1Reflection_plane12]
      calc
        normalizedSpecialUnitaryRealTrace N
            (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A *
              (periodicHypercubicPlaquetteHolonomy A
                (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12))⁻¹ *
              (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A)⁻¹) =
            normalizedSpecialUnitaryRealTrace N
              (periodicHypercubicPlaquetteHolonomy A
                (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12))⁻¹ :=
          normalizedSpecialUnitaryRealTrace_conjInvariant
            (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A)
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12))⁻¹
        _ = normalizedSpecialUnitaryRealTrace N
              (periodicHypercubicPlaquetteHolonomy A
                (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12)) :=
          normalizedSpecialUnitaryRealTrace_inv _
  | plane13 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_axis1Reflection_plane13]
      calc
        normalizedSpecialUnitaryRealTrace N
            (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A *
              (periodicHypercubicPlaquetteHolonomy A
                (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13))⁻¹ *
              (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A)⁻¹) =
            normalizedSpecialUnitaryRealTrace N
              (periodicHypercubicPlaquetteHolonomy A
                (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13))⁻¹ :=
          normalizedSpecialUnitaryRealTrace_conjInvariant
            (periodicHypercubicEvenSpatialAxis1ReflectionConjugator a A)
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13))⁻¹
        _ = normalizedSpecialUnitaryRealTrace N
              (periodicHypercubicPlaquetteHolonomy A
                (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13)) :=
          normalizedSpecialUnitaryRealTrace_inv _
  | plane23 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_axis1Reflection_plane23]

/-- Every fixed-plane zero-momentum component is invariant under the independent axis-`1`
reflection. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_axis1ReflectionInvariant
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane
        (periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A) =
      periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  rw [← Equiv.sum_comp
    (periodicHypercubicEvenSpatialPlaneAxis1ReflectionRebaseEquiv H plane)]
  apply Finset.sum_congr rfl
  intro a _ha
  exact periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_axis1Reflection
    H N plane a A

/-- The equal-weight all-spatial zero-momentum normalized-real-trace observable is invariant under
reflection of spatial axis `1`. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_axis1ReflectionInvariant
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenConfigurationSpatialAxis1Reflection H A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
  apply Finset.sum_congr rfl
  intro plane _hplane
  exact periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_axis1ReflectionInvariant
    H N plane A

end

end MathlibAnalytic
end MGAP4D
