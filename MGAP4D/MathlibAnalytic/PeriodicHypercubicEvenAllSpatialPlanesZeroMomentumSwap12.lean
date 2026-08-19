import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialAxisSwap12Geometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedRealTraceInversion
import Mathlib.Tactic

/-!
# Swap `(1 2)` invariance of the all-spatial zero-momentum plaquette operator

The preceding geometry layer constructs the spatial-axis transposition `(1 2)` on vertices,
positive links, configurations, time-zero displacements, and the three spatial-plane labels.
This file transports actual plaquette holonomies through that reindexing.

For the canonical plane orientations the transformation is exact:

* `(1,2)` is geometrically fixed but its boundary orientation reverses, hence its holonomy is
  inverted;
* `(1,3)` is carried to `(2,3)` with orientation preserved;
* `(2,3)` is carried to `(1,3)` with orientation preserved.

The normalized real trace removes the orientation reversal by the already-canonical inversion
identity.  Reindexing the finite displacement and plane sums then proves invariance of the full
all-spatial zero-momentum observable under this spatial permutation generator.

This is a finite-lattice cubic-symmetry receipt for one generator only.  No continuum-spin or
spectral claim is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap12Equiv_symm_eq
    (n : ℕ) (x : PeriodicHypercubicVertex n) :
    (periodicHypercubicVertexSpatialAxisSwap12Equiv n).symm x =
      periodicHypercubicVertexSpatialAxisSwap12Equiv n x := by
  funext i
  simp

@[simp]
theorem periodicHypercubicVertexSpatialAxisSwap12Equiv_involutive
    (n : ℕ) (x : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexSpatialAxisSwap12Equiv n
        (periodicHypercubicVertexSpatialAxisSwap12Equiv n x) = x := by
  rw [← periodicHypercubicVertexSpatialAxisSwap12Equiv_symm_eq]
  exact (periodicHypercubicVertexSpatialAxisSwap12Equiv n).symm_apply_apply x

@[simp]
theorem periodicHypercubicEdgeSpatialAxisSwap12Equiv_symm_eq
    (n : ℕ) (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeSpatialAxisSwap12Equiv n).symm e =
      periodicHypercubicEdgeSpatialAxisSwap12Equiv n e := by
  rcases e with ⟨x, mu⟩
  simp [periodicHypercubicEdgeSpatialAxisSwap12Equiv]

@[simp]
theorem periodicHypercubicConfigurationSpatialAxisSwap12_apply
    {n : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicConfigurationSpatialAxisSwap12 A e =
      A (periodicHypercubicEdgeSpatialAxisSwap12Equiv n e) := by
  simp [periodicHypercubicConfigurationSpatialAxisSwap12]

/-- On the `(1,2)` plane the spatial transposition reverses the canonical plaquette orientation. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap12_plane12
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationSpatialAxisSwap12 A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialDisplacementSwap12Equiv H a)
          .plane12) =
      (periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane12))⁻¹ := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    periodicHypercubicEvenSpatialDisplacementSwap12Equiv,
    periodicHypercubicEdgeSpatialAxisSwap12Equiv,
    periodicHypercubicVertexSpatialAxisSwap12Equiv_shift]
  group

/-- The `(1,3)` plane is carried to `(2,3)` with the canonical orientation preserved. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap12_plane13
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationSpatialAxisSwap12 A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialDisplacementSwap12Equiv H a)
          .plane23) =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane13) := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    periodicHypercubicEvenSpatialDisplacementSwap12Equiv,
    periodicHypercubicEdgeSpatialAxisSwap12Equiv,
    periodicHypercubicVertexSpatialAxisSwap12Equiv_shift]

/-- The `(2,3)` plane is carried to `(1,3)` with the canonical orientation preserved. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap12_plane23
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationSpatialAxisSwap12 A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialDisplacementSwap12Equiv H a)
          .plane13) =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenSpatialPlanePlaquette H a .plane23) := by
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenSpatialPlanePlaquette,
    periodicHypercubicEvenSpatialDisplacementSwap12Equiv,
    periodicHypercubicEdgeSpatialAxisSwap12Equiv,
    periodicHypercubicVertexSpatialAxisSwap12Equiv_shift]

/-- The normalized real trace is equivariant under the `(1 2)` spatial-axis swap after relabelling
both the spatial displacement and the spatial plane. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_swap12
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N
        (periodicHypercubicSpatialPlaneSwap12Equiv plane)
        (periodicHypercubicEvenSpatialDisplacementSwap12Equiv H a)
        (periodicHypercubicConfigurationSpatialAxisSwap12 A) =
      periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A := by
  cases plane with
  | plane12 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap12_plane12]
      exact normalizedSpecialUnitaryRealTrace_inv _
  | plane13 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap12_plane13]
  | plane23 =>
      unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
      rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_swap12_plane23]

/-- Each fixed-plane zero-momentum component is carried to the correspondingly relabelled plane by
the spatial transposition. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_swap12
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N
        (periodicHypercubicSpatialPlaneSwap12Equiv plane)
        (periodicHypercubicConfigurationSpatialAxisSwap12 A) =
      periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  refine Fintype.sum_equiv
    (periodicHypercubicEvenSpatialDisplacementSwap12Equiv H).symm _ _ ?_
  intro a
  have h :=
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_swap12
      H N plane
      ((periodicHypercubicEvenSpatialDisplacementSwap12Equiv H).symm a) A
  simpa using h

/-- The equal-weight all-spatial zero-momentum plaquette observable is exactly invariant under the
spatial permutation generator swapping axes `1` and `2`. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_swap12Invariant
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicConfigurationSpatialAxisSwap12 A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
  refine Fintype.sum_equiv periodicHypercubicSpatialPlaneSwap12Equiv.symm _ _ ?_
  intro plane
  have h :=
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_swap12
      H N (periodicHypercubicSpatialPlaneSwap12Equiv.symm plane) A
  simpa using h

end

end MathlibAnalytic
end MGAP4D
