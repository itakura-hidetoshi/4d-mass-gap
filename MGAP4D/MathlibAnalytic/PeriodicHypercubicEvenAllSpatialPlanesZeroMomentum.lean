import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentum
import Mathlib.Tactic

/-!
# All-spatial-plane zero-momentum plaquette operator

The fixed `(1,2)` zero-momentum plaquette sum is now canonical.  A scalar glueball precursor should
not privilege one spatial coordinate plane, so the next additive step is to include the three
spatial planes `(1,2)`, `(1,3)`, and `(2,3)` with equal weight.

This file introduces exactly those three plane labels, constructs the corresponding time-zero
plaquettes and normalized-real-trace orbit sums, proves spatial translation invariance plane by
plane, and then proves spatial translation invariance of their total sum.  The `(1,2)` component is
identified with the already canonical fixed-plane zero-momentum operator from the preceding layer.

The equal-weight three-plane sum is the natural cubic-scalar **precursor**, but this file does not
claim the `A₁⁺⁺` label.  That label requires explicit theorem-generated cubic rotation, parity, and
charge-conjugation transformation laws, which remain downstream.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The three purely spatial coordinate planes in four Euclidean dimensions. -/
inductive PeriodicHypercubicSpatialPlane where
  | plane12
  | plane13
  | plane23
  deriving DecidableEq, Fintype

/-- Ordered coordinate-axis pair carried by a spatial plane label. -/
def PeriodicHypercubicSpatialPlane.axisPair :
    PeriodicHypercubicSpatialPlane → PeriodicHypercubicAxisPair
  | .plane12 => ⟨((1 : PeriodicHypercubicAxis), (2 : PeriodicHypercubicAxis)), by decide⟩
  | .plane13 => ⟨((1 : PeriodicHypercubicAxis), (3 : PeriodicHypercubicAxis)), by decide⟩
  | .plane23 => ⟨((2 : PeriodicHypercubicAxis), (3 : PeriodicHypercubicAxis)), by decide⟩

@[simp]
theorem PeriodicHypercubicSpatialPlane.axisPair_plane12 :
    PeriodicHypercubicSpatialPlane.axisPair .plane12 =
      ⟨((1 : PeriodicHypercubicAxis), (2 : PeriodicHypercubicAxis)), by decide⟩ :=
  rfl

@[simp]
theorem PeriodicHypercubicSpatialPlane.axisPair_plane13 :
    PeriodicHypercubicSpatialPlane.axisPair .plane13 =
      ⟨((1 : PeriodicHypercubicAxis), (3 : PeriodicHypercubicAxis)), by decide⟩ :=
  rfl

@[simp]
theorem PeriodicHypercubicSpatialPlane.axisPair_plane23 :
    PeriodicHypercubicSpatialPlane.axisPair .plane23 =
      ⟨((2 : PeriodicHypercubicAxis), (3 : PeriodicHypercubicAxis)), by decide⟩ :=
  rfl

/-- A purely spatial plaquette at the translated time-zero base point. -/
def periodicHypercubicEvenSpatialPlanePlaquette
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (plane : PeriodicHypercubicSpatialPlane) :
    PeriodicHypercubicEvenPlaquette H :=
  (a.1, plane.axisPair)

@[simp]
theorem periodicHypercubicEvenSpatialPlanePlaquette_base_time
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (plane : PeriodicHypercubicSpatialPlane) :
    (periodicHypercubicEvenSpatialPlanePlaquette H a plane).1 0 = 0 :=
  a.2

/-- The `(1,2)` member of the three-plane family is exactly the previously constructed translated
primary plaquette. -/
theorem periodicHypercubicEvenSpatialPlanePlaquette_plane12_eq_primaryTranslate
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicEvenSpatialPlanePlaquette H a .plane12 =
      periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a := by
  apply Prod.ext
  · simp [periodicHypercubicEvenSpatialPlanePlaquette]
  · rfl

/-- A further spatial translation shifts only the orbit label, for every one of the three spatial
coordinate planes. -/
theorem periodicHypercubicEvenSpatialPlanePlaquette_translate_add
    (H : ℕ)
    (a b : PeriodicHypercubicEvenSpatialDisplacement H)
    (plane : PeriodicHypercubicSpatialPlane) :
    periodicHypercubicPlaquetteTranslationEquiv
        (PeriodicHypercubicEvenSideLength H) b.1
        (periodicHypercubicEvenSpatialPlanePlaquette H a plane) =
      periodicHypercubicEvenSpatialPlanePlaquette H
        (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b a) plane := by
  apply Prod.ext
  · simp [periodicHypercubicEvenSpatialPlanePlaquette,
      periodicHypercubicEvenSpatialDisplacementTranslationEquiv, add_assoc]
  · rfl

/-- Normalized real trace of one translated plaquette in a chosen spatial plane. -/
noncomputable def periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  normalizedSpecialUnitaryRealTrace N
    (periodicHypercubicPlaquetteHolonomy A
      (periodicHypercubicEvenSpatialPlanePlaquette H a plane))

/-- The `(1,2)` translated trace agrees exactly with the canonical primary-plaquette orbit. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_plane12_eq_primary
    (H N : ℕ)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N .plane12 a A =
      periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N a A := by
  unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
  rw [periodicHypercubicEvenSpatialPlanePlaquette_plane12_eq_primaryTranslate]
  rfl

local instance allSpatialPlanesMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Exact label-shift covariance for every spatial plane. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_translationShift
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a b : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane
        (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b a)
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) b.1 A) =
      periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A := by
  unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
  have h :=
    periodicHypercubicPlaquetteHolonomy_configurationTranslation
      b.1 A (periodicHypercubicEvenSpatialPlanePlaquette H a plane)
  rw [periodicHypercubicEvenSpatialPlanePlaquette_translate_add H a b plane] at h
  exact congrArg (normalizedSpecialUnitaryRealTrace N) h

/-- Zero-spatial-momentum sum in one chosen spatial coordinate plane. -/
noncomputable def periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ := by
  classical
  exact ∑ a : PeriodicHypercubicEvenSpatialDisplacement H,
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A

/-- The `(1,2)` zero-momentum component is exactly the previously canonical fixed-plane operator. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_plane12_eq_primary
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N .plane12 A =
      periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace
  apply Finset.sum_congr rfl
  intro a _ha
  exact
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_plane12_eq_primary
      H N a A

/-- Each spatial-plane zero-momentum component is exactly invariant under periodic spatial
translations of the same finite Wilson configuration. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_translationInvariant
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (b : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) b.1 A) =
      periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  refine Fintype.sum_equiv
    (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b).symm _ _ ?_
  intro a
  have h :=
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_translationShift
      H N plane
      ((periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b).symm a)
      b A
  simpa using h

/-- Equal-weight sum over the three purely spatial zero-momentum plaquette components. -/
noncomputable def periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ := by
  classical
  exact ∑ plane : PeriodicHypercubicSpatialPlane,
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A

/-- The full equal-weight three-plane zero-momentum operator is exactly invariant under every
periodic spatial translation. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_translationInvariant
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) b.1 A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
  apply Finset.sum_congr rfl
  intro plane _hplane
  exact
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_translationInvariant
      H N plane b A

end

end MathlibAnalytic
end MGAP4D
