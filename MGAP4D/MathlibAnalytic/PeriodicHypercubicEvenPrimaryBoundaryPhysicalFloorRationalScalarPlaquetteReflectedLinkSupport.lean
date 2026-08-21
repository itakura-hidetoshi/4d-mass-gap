import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquetteLinkSupport
import Mathlib.Tactic

/-!
# Reflected physical-link support of a primary scalar coordinate

The positive-time scalar plaquette coordinate already has an exact four-link
support.  A negative coordinate of the reflection-completed path is, by
definition, the corresponding positive coordinate evaluated on the reflected
finite Wilson configuration.  This file pulls that dependence back to the
original finite configuration.

For a nonnegative rational slot `q`, the reflected support is simply the image
of the positive four-link support under the concrete physical edge reflection.
Agreement of two full finite configurations on that reflected support is enough
to identify the scalar coordinate at time `-q`.

This is a finite support statement only.  It introduces no covariance-decay
estimate, Dobrushin threshold, positive mass, Hamiltonian gap, or identification
of stochastic update time with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The physical-link support in the original Wilson configuration that controls
one negative reflection-completed scalar coordinate. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ) : Finset (PeriodicHypercubicEvenEdge H) :=
  (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
      H latticeSpacing n q).image
    (periodicHypercubicEvenEdgeReflection H)

/-- Every edge in the positive scalar support has its reflected physical edge
in the reflected support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_reflection_mem_reflectedSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (k : Fin 4) :
    periodicHypercubicEvenEdgeReflection H
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k) ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
        H latticeSpacing n q := by
  classical
  exact Finset.mem_image.mpr ⟨
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
      H latticeSpacing n q k,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_mem_support
      H latticeSpacing n q k,
    rfl⟩

/-- Agreement on the reflected physical support implies agreement of the two
reflected full configurations on the positive scalar support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquette_reflectedConfiguration_agreeOnSupport
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (A B : PeriodicHypercubicEvenEdge H → Gauge)
    (hAB : ∀ e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
        H latticeSpacing n q,
      A e = B e) :
    ∀ e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
        H latticeSpacing n q,
      periodicHypercubicEvenConfigurationReflection H A e =
        periodicHypercubicEvenConfigurationReflection H B e := by
  intro e he
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport at hAB
  have href :
      A (periodicHypercubicEvenEdgeReflection H e) =
        B (periodicHypercubicEvenEdgeReflection H e) := by
    apply hAB
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  by_cases htime : e.2 = 0
  · simp [periodicHypercubicEvenConfigurationReflection, htime, href]
  · simp [periodicHypercubicEvenConfigurationReflection, htime, href]

/-- A negative reflection-completed scalar coordinate depends only on the
reflected image of the four positive-time physical links. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_neg_eq_of_eqOn_reflectedSupport
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hq : 0 ≤ q)
    (A B :
      PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
        H latticeSpacing n q,
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) (-q) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n B) (-q) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [neg_zero]
    rw [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
        H latticeSpacing n A 0 le_rfl,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
        H latticeSpacing n B 0 le_rfl]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_eq_of_eqOn_support
        H N latticeSpacing n 0 A B hAB
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hneg : -q < 0 := neg_neg.mpr hqpos
    rw [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_negative
        H latticeSpacing n A (-q) hneg,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_negative
        H latticeSpacing n B (-q) hneg]
    simp only [neg_neg]
    apply
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_eq_of_eqOn_support
        H N latticeSpacing n q
        (periodicHypercubicEvenConfigurationReflection H A)
        (periodicHypercubicEvenConfigurationReflection H B)
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquette_reflectedConfiguration_agreeOnSupport
        H latticeSpacing n q A B hAB

end

end MathlibAnalytic
end MGAP4D
