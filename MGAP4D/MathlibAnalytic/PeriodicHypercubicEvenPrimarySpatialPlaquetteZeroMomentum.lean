import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteTranslationOrbit
import Mathlib.Tactic

/-!
# Zero-spatial-momentum projection of the primary plaquette orbit

The preceding translation-orbit layer constructs the canonical `(1,2)` spatial plaquette at every
periodic displacement tangent to the time-zero slice.  The first genuine glueball-channel operation
is the zero-spatial-momentum projection: sum the same gauge-invariant normalized-trace plaquette
over that complete finite spatial orbit.

This file constructs that finite sum and proves, without a new physical assumption, that it is
invariant under every periodic spatial translation of the underlying finite Wilson configuration.
The proof is purely same-root: reindex the finite orbit by the translation equivalence and use the
canonical plaquette-holonomy translation identity.

This is still a fixed `(1,2)` plane operator.  It is therefore a zero-momentum scalar-valued
plaquette operator, not yet a proved cubic `A₁⁺⁺` / continuum `Jᴾᶜ = 0⁺⁺` glueball operator.
A later layer must combine the three spatial coordinate planes and prove the relevant parity,
charge-conjugation, and cubic-symmetry receipts.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Right translation of the finite spatial-displacement carrier. -/
noncomputable def periodicHypercubicEvenSpatialDisplacementTranslationEquiv
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpatialDisplacement H) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun a :=
    ⟨a.1 + b.1, by
      change a.1 0 + b.1 0 = 0
      rw [a.2, b.2]
      simp⟩
  invFun a :=
    ⟨a.1 - b.1, by
      change a.1 0 - b.1 0 = 0
      rw [a.2, b.2]
      simp⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    simp
  right_inv a := by
    apply Subtype.ext
    funext i
    simp

@[simp]
theorem periodicHypercubicEvenSpatialDisplacementTranslationEquiv_apply_val
    (H : ℕ)
    (b a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b a).1 =
      a.1 + b.1 :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialDisplacementTranslationEquiv_symm_apply_val
    (H : ℕ)
    (b a : PeriodicHypercubicEvenSpatialDisplacement H) :
    ((periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b).symm a).1 =
      a.1 - b.1 :=
  rfl

/-- Translating an already translated primary plaquette by `b` is the same as translating it by
`a+b` in one step. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_add
    (H : ℕ)
    (a b : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicPlaquetteTranslationEquiv
        (PeriodicHypercubicEvenSideLength H) b.1
        (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a) =
      periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H
        (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b a) := by
  apply Prod.ext
  · simp [periodicHypercubicEvenPrimarySpatialPlaquetteTranslate,
      periodicHypercubicEvenSpatialDisplacementTranslationEquiv, add_assoc]
  · rfl

local instance zeroMomentumPlaquetteMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Exact covariance of the translated normalized-trace family under a further spatial source
translation.  The label is shifted by the same displacement. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace_translationShift
    (H N : ℕ)
    (a b : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N
        (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b a)
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) b.1 A) =
      periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N a A := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace
  have h :=
    periodicHypercubicPlaquetteHolonomy_configurationTranslation
      b.1 A (periodicHypercubicEvenPrimarySpatialPlaquetteTranslate H a)
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTranslate_add H a b] at h
  exact congrArg (normalizedSpecialUnitaryRealTrace N) h

/-- Unnormalized zero-spatial-momentum projection of the canonical fixed-plane plaquette trace.
Using the sum rather than an average avoids inserting any nonzero-cardinality side condition and is
the standard finite-volume zero-momentum projection up to an irrelevant normalization factor. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ := by
  classical
  exact ∑ a : PeriodicHypercubicEvenSpatialDisplacement H,
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace H N a A

/-- The zero-momentum plaquette sum is exactly invariant under every periodic spatial translation
of the same finite Wilson configuration. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace_translationInvariant
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace H N
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) b.1 A) =
      periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteZeroMomentumNormalizedTrace
  refine Fintype.sum_equiv
    (periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b).symm _ _ ?_
  intro a
  have h :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTranslatedNormalizedTrace_translationShift
      H N
      ((periodicHypercubicEvenSpatialDisplacementTranslationEquiv H b).symm a)
      b A
  simpa using h

end

end MathlibAnalytic
end MGAP4D
