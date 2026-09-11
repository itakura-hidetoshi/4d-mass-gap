import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquetteLinkSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumReflectionInvariance
import Mathlib.Tactic

/-!
# Reflected physical-link support of the primary scalar plaquette coordinate

The canonical midpoint covariance uses negative rational coordinates from the
reflection-completed primary scalar path.  Positive coordinates already have a
literal four-link support.  This file pulls that support through the actual
finite Euclidean reflection.

For a nonnegative rational slot `q`, define the reflected support as the image
of the positive four-link support under the oriented positive-edge reflection.
Agreement of two full finite configurations on that reflected support implies
agreement of their reflected configurations on the original positive support.
Combining this with the exact scalar reflection covariance proves that the
negative scalar coordinate at `-q` depends only on the reflected support.

This is finite support geometry only.  No covariance decay, Dobrushin
threshold, continuum premise, stochastic-time identification, positive mass,
or Hamiltonian gap is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Physical-link support in the original Wilson source of the reflected scalar
coordinate at `-q`, obtained by reflecting every edge in the positive support
at `q`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) := by
  classical
  exact
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
      H latticeSpacing n q).image
        (periodicHypercubicEvenEdgeReflection H)

/-- Reflection sends every edge in the positive scalar support into the
reflected scalar support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_mem_reflectedSupport_of_mem
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n q) :
    periodicHypercubicEvenEdgeReflection H e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
        H latticeSpacing n q := by
  classical
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- In particular, the reflected image of each of the four literal plaquette
links belongs to the reflected support. -/
@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_mem_reflectedSupport
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
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_mem_reflectedSupport_of_mem
      H latticeSpacing n q _
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_mem_support
        H latticeSpacing n q k)

/-- Agreement on the reflected support is exactly what is needed for the two
reflected finite configurations to agree on the original positive support. -/
theorem
    periodicHypercubicEvenConfigurationReflection_eq_of_eqOn_primaryScalarPlaquetteReflectedSupport
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (A B : PeriodicHypercubicEvenEdge H → Gauge)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q →
      A e = B e)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n q) :
    periodicHypercubicEvenConfigurationReflection H A e =
      periodicHypercubicEvenConfigurationReflection H B e := by
  have href :
      periodicHypercubicEvenEdgeReflection H e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_mem_reflectedSupport_of_mem
      H latticeSpacing n q e he
  unfold periodicHypercubicEvenConfigurationReflection
  by_cases htime : e.2 = 0
  · rw [if_pos htime, if_pos htime, hAB _ href]
  · rw [if_neg htime, if_neg htime]
    exact hAB _ href

/-- The negative reflection-completed scalar coordinate at `-q` depends only on
the reflected physical four-link support at the corresponding nonnegative slot
`q`.  The proof includes `q = 0` uniformly through exact scalar reflection
covariance. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_neg_eq_of_eqOn_reflectedSupport
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hq : 0 ≤ q)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q →
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) (-q) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n B) (-q) := by
  have hreflected : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n q →
      periodicHypercubicEvenConfigurationReflection H A e =
        periodicHypercubicEvenConfigurationReflection H B e := by
    intro e he
    exact
      periodicHypercubicEvenConfigurationReflection_eq_of_eqOn_primaryScalarPlaquetteReflectedSupport
        H latticeSpacing n q A B hAB e he
  have hpositive :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_eq_of_eqOn_support
      H N latticeSpacing n q hq
      (periodicHypercubicEvenConfigurationReflection H A)
      (periodicHypercubicEvenConfigurationReflection H B)
      hreflected
  have hcovA := congrFun
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectionCompletedReadout_configurationReflection
      H N latticeSpacing n A) q
  have hcovB := congrFun
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectionCompletedReadout_configurationReflection
      H N latticeSpacing n B) q
  calc
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) (-q) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n
          (periodicHypercubicEvenConfigurationReflection H A)) q := by
        simpa [
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection] using
          hcovA.symm
    _ =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n
          (periodicHypercubicEvenConfigurationReflection H B)) q := hpositive
    _ =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n B) (-q) := by
        simpa [
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection] using
          hcovB

end

end MathlibAnalytic
end MGAP4D
