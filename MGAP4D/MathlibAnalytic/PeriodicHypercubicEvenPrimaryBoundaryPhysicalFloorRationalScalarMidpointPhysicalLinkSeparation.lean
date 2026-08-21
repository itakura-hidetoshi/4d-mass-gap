import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointPhysicalLinkSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import Mathlib.Tactic

/-!
# Reflection-side separation of fixed-slot primary scalar midpoint supports

The preceding layer packages the literal finite Wilson-link supports of the
left reflected midpoint observable and the translated right midpoint observable.
This file proves their first geometric separation statement using only the
existing physical reflection-orbit side classification.

A primary scalar plaquette edge whose physical-floor step stays within the
primary half extent is spatial and is never on the negative reflection side.
Its reflected image is therefore never positive.  If the translated right
physical-floor step is strictly positive and still at most `H`, every right
plaquette edge is on the positive reflection side.  Hence the reflected-left
and translated-right finite supports are disjoint.  The result is then lifted
from one coordinate pair to the finite unions over an arbitrary fixed slot set.

This is finite Euclidean-link geometry only.  It gives disjointness, not yet a
metric distance lower bound or a covariance estimate.  No Dobrushin threshold,
heat-bath/update-time identification, positive mass, or Hamiltonian gap is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every translated primary scalar plaquette link remains spatial. -/
@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_direction_ne_zero
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (k : Fin 4) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
      H latticeSpacing n q k).2 ≠ 0 := by
  simpa [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge,
    periodicHypercubicEdgeTranslationEquiv] using
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge_direction_ne_zero H k)

/-- Before wraparound, a translated primary scalar plaquette link is never on
the negative reflection side.  Floor step zero is fixed; positive floor steps
through `H` are positive. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_side_ne_negative
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (k : Fin 4) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k) ≠
      ReflectionEdgeSide.negative := by
  let m : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n)
  have hval :
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k).1 0).val = m := by
    simpa [m] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
        H latticeSpacing n q hwithin k
  have hspace :
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
        H latticeSpacing n q k).2 ≠ 0 :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_direction_ne_zero
      H latticeSpacing n q k
  by_cases hm : m = 0
  · rw [periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
      H _ hspace (by simpa [hval] using hm)]
    decide
  · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hpos :
        1 ≤
          ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n q k).1 0).val := by
      rw [hval]
      exact hmpos
    have hle :
        ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n q k).1 0).val ≤ H := by
      rw [hval]
      exact hwithin
    rw [periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
      H _ hspace hpos hle]
    decide

/-- A strictly positive primary physical-floor step through `H` puts every
translated scalar plaquette link on the positive reflection side. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_side_positive
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hpos :
      1 ≤ Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n))
    (hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (k : Fin 4) :
    periodicHypercubicEvenEdgeSide H
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k) =
      ReflectionEdgeSide.positive := by
  have hval :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
      H latticeSpacing n q hwithin k
  have hspace :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_direction_ne_zero
      H latticeSpacing n q k
  apply periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val H _ hspace
  · simpa [hval] using hpos
  · simpa [hval] using hwithin

/-- Every edge in one admissible positive scalar support is never negative. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_side_ne_negative
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n q) :
    periodicHypercubicEvenEdgeSide H e ≠ ReflectionEdgeSide.negative := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport,
    Finset.mem_image, Finset.mem_univ, true_and] at he
  rcases he with ⟨k, rfl⟩
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_side_ne_negative
      H latticeSpacing n q hwithin k

/-- Every edge in one strictly-positive admissible scalar support lies on the
positive reflection side. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_side_positive
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hpos :
      1 ≤ Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n))
    (hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n q) :
    periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport,
    Finset.mem_image, Finset.mem_univ, true_and] at he
  rcases he with ⟨k, rfl⟩
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_side_positive
      H latticeSpacing n q hpos hwithin k

/-- Reflection of an admissible positive scalar support can never lie on the
positive reflection side. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_side_ne_positive
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q) :
    periodicHypercubicEvenEdgeSide H e ≠ ReflectionEdgeSide.positive := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport,
    Finset.mem_image] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  have hside :
      periodicHypercubicEvenEdgeSide H e₀ ≠ ReflectionEdgeSide.negative :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_side_ne_negative
      H latticeSpacing n q hwithin e₀ he₀
  rw [periodicHypercubicEvenEdgeSide_reflection]
  cases hs : periodicHypercubicEvenEdgeSide H e₀ <;>
    simp [hs] at hside ⊢

/-- A reflected-left single-coordinate support is disjoint from a translated
right single-coordinate support whenever the left floor stays within the
primary half and the right floor lies in `1, ..., H`. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_disjoint_support_of_right_floor_positive
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (qLeft qRight : ℚ)
    (hleftWithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) ≤ H)
    (hrightPos :
      1 ≤ Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n))
    (hrightWithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n) ≤ H) :
    Disjoint
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
        H latticeSpacing n qLeft)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
        H latticeSpacing n qRight) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro e hleft hright
  have hne :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_side_ne_positive
      H latticeSpacing n qLeft hleftWithin e hleft
  have hpos :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_side_positive
      H latticeSpacing n qRight hrightPos hrightWithin e hright
  exact hne hpos

/-- The complete finite reflected-left midpoint support is disjoint from the
complete finite translated-right midpoint support when every left floor stays
within the primary half and every translated right floor lies in `1, ..., H`.

This is the finite-set separation theorem needed before introducing an explicit
physical support-distance parameter. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_disjoint_rightSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightPos : ∀ q : ℚ, q ∈ J →
      1 ≤ Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n))
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H) :
    Disjoint
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro e hleft hright
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport,
    Finset.mem_biUnion] at hleft
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport,
    Finset.mem_biUnion] at hright
  rcases hleft with ⟨qLeft, hqLeft, heLeft⟩
  rcases hright with ⟨qRight, hqRight, heRight⟩
  have hne :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_side_ne_positive
      H latticeSpacing n qLeft (hleftWithin qLeft hqLeft) e heLeft
  have hpos :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_side_positive
      H latticeSpacing n ((qRight + r) + r)
      (hrightPos qRight hqRight) (hrightWithin qRight hqRight) e heRight
  exact hne hpos

end

end MathlibAnalytic
end MGAP4D
