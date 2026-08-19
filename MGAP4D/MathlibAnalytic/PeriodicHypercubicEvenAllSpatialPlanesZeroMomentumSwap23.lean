import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialAxisSwap23Geometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedRealTraceInversion
import Mathlib.Tactic

/-!
# Swap `(2 3)` invariance of the all-spatial zero-momentum plaquette operator

The canonical geometry now contains both adjacent spatial transpositions.  This file transports
actual plaquette holonomies through the second generator `(2 3)` and proves invariance of the
all-spatial zero-momentum normalized-trace observable.

For the canonical plane orientations:

* `(1,2)` is carried to `(1,3)` with orientation preserved;
* `(1,3)` is carried to `(1,2)` with orientation preserved;
* `(2,3)` is geometrically fixed but its canonical boundary orientation reverses, so the holonomy
  is inverted.

The canonical normalized-real-trace inversion theorem removes the last orientation reversal.
Finite reindexing of the displacement and plane sums then gives exact invariance under swap `(2 3)`.
Together with the already-canonical swap `(1 2)` theorem, this supplies observable-level invariance
under the two adjacent generators of all permutations of the three spatial axes.  This file still
does not claim parity, charge conjugation, continuum spin, or a spectral mass statement.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap23Equiv_symm_eq
    (n : ℕ) (x : PeriodicHypercubicVertex n) :
    (periodicHypercubicVertexSpatialAxisSwap23Equiv n).symm x =
      periodicHypercubicVertexSpatialAxisSwap23Equiv n x := by
  funext i
  simp

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap23Equiv_involutive
    (n : ℕ) (x : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexSpatialAxisSwap23Equiv n
        (periodicHypercubicVertexSpatialAxisSwap23Equiv n x) = x := by
  rw [← periodicHypercubicVertexSpatialAxisSwap23Equiv_symm_eq]
  exact (periodicHypercubicVertexSpatialAxisSwap23Equiv n).symm_apply_apply x

@[simp]
theorem periodicHypercubicEdgeSpatialAxisSwap23Equiv_symm_eq
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeSpatialAxisSwap23Equiv n).symm e =
      periodicHypercubicEdgeSpatialAxisSwap23Equiv n e := by
  rcases e with ⟨x, mu⟩
  simp [periodicHypercubicEdgeSpatialAxisSwap23Equiv]

@[simp]
theorem periodicHypercubicConfigurationSpatialAxisSwap23_apply
    {n : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicConfigurationSpatialAxisSwap23 A e =
      A (periodicHypercubicEdgeSpatialAxisSwap23Equiv n e) := by
  simp [periodicHypercubicConfigurationSpatialAxisSwap23]

/-- The `(1,2)` plane is carried to `(1,3)` with canonical orientation preserved. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap23_plane12
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationSpatialAxisSwap23 A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialDisplacementSwap23Equiv H a)
          .plane13) =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12) := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    periodicHypercubicEvenSpatialDisplacementSwap23Equiv,
    periodicHypercubicEdgeSpatialAxisSwap23Equiv,
    periodicHypercubicVertexSpatialAxisSwap23Equiv_shift]

/-- The `(1,3)` plane is carried to `(1,2)` with canonical orientation preserved. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap23_plane13
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationSpatialAxisSwap23 A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialDisplacementSwap23Equiv H a)
          .plane12) =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13) := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    periodicHypercubicEvenSpatialDisplacementSwap23Equiv,
    periodicHypercubicEdgeSpatialAxisSwap23Equiv,
    periodicHypercubicVertexSpatialAxisSwap23Equiv_shift]

/-- On the `(2,3)` plane the spatial transposition reverses the canonical plaquette orientation. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap23_plane23
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationSpatialAxisSwap23 A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialDisplacementSwap23Equiv H a)
          .plane23) =
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane23))⁻¹ := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    periodicHypercubicEvenSpatialDisplacementSwap23Equiv,
    periodicHypercubicEdgeSpatialAxisSwap23Equiv,
    periodicHypercubicVertexSpatialAxisSwap23Equiv_shift]
  group

/-- The normalized real trace is equivariant under the `(2 3)` spatial-axis swap after relabelling
both the spatial displacement and the spatial plane. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_swap23
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N
        (periodicHypercubicSpatialPlaneSwap23Equiv plane)
        (periodicHypercubicEvenSpatialDisplacementSwap23Equiv H a)
        (periodicHypercubicConfigurationSpatialAxisSwap23 A) =
      periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A := by
  cases plane with
  | plane12 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicSpatialPlaneSwap23Equiv_plane12]
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap23_plane12]
  | plane13 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicSpatialPlaneSwap23Equiv_plane13]
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap23_plane13]
  | plane23 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicSpatialPlaneSwap23Equiv_plane23]
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap23_plane23]
      exact normalizedSpecialUnitaryRealTrace_inv _

/-- Each fixed-plane zero-momentum component is carried to the correspondingly relabelled plane by
the spatial transposition. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_swap23
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N
        (periodicHypercubicSpatialPlaneSwap23Equiv plane)
        (periodicHypercubicConfigurationSpatialAxisSwap23 A) =
      periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  refine Fintype.sum_equiv
    (periodicHypercubicEvenSpatialDisplacementSwap23Equiv H).symm _ _ ?_
  intro a
  have h :=
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_swap23
      H N plane
      ((periodicHypercubicEvenSpatialDisplacementSwap23Equiv H).symm a) A
  simpa using h

/-- The equal-weight all-spatial zero-momentum plaquette observable is exactly invariant under the
spatial permutation generator swapping axes `2` and `3`. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_swap23Invariant
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicConfigurationSpatialAxisSwap23 A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
  refine Fintype.sum_equiv periodicHypercubicSpatialPlaneSwap23Equiv.symm _ _ ?_
  intro plane
  have h :=
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_swap23
      H N (periodicHypercubicSpatialPlaneSwap23Equiv.symm plane) A
  simpa using h

end

end MathlibAnalytic
end MGAP4D
