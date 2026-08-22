import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointPhysicalLinkSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import Mathlib.Tactic

/-!
# Uniform cardinality bounds for midpoint Wilson supports

Each primary scalar coordinate reads at most the four physical links of one
orientation-correct plaquette.  The reflected coordinate is obtained by an edge
reflection image, so it also uses at most four links.  Taking the finite union
over a slot set `J` therefore gives left and right midpoint supports of size at
most `4 * J.card`, independently of lattice volume, scale, spacing, and
translation.  The combined midpoint support has size at most `8 * J.card`.

These are purely finite combinatorial bounds.  No covariance estimate,
Dobrushin threshold, continuum limit, or mass-gap statement is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- One nonnegative primary scalar plaquette coordinate reads at most four
physical Wilson links. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_card_le_four
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
      H latticeSpacing n q).card ≤ 4 := by
  classical
  unfold
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
  calc
    (Finset.univ.image fun k : Fin 4 =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k).card ≤
      (Finset.univ : Finset (Fin 4)).card :=
        Finset.card_image_le
    _ = 4 := by simp

/-- Reflection does not increase the four-link support cardinality. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_card_le_four
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
      H latticeSpacing n q).card ≤ 4 := by
  classical
  unfold
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
  exact le_trans Finset.card_image_le
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_card_le_four
      H latticeSpacing n q)

/-- The reflected-left fixed-slot midpoint support has at most four links per
slot, uniformly in finite volume and lattice scale. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_card_le
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
      H latticeSpacing n J).card ≤ 4 * J.card := by
  classical
  calc
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J).card ≤
      ∑ q ∈ J,
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q).card := by
      unfold
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
      exact finset_card_biUnion_le_sum_card J fun q =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q
    _ ≤ ∑ _q ∈ J, 4 := by
      apply Finset.sum_le_sum
      intro q hq
      exact
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_card_le_four
          H latticeSpacing n q
    _ = 4 * J.card := by
      simp [Nat.mul_comm]

/-- The translated-right fixed-slot midpoint support has at most four links per
slot, uniformly in the translation parameter. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport_card_le
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
      H latticeSpacing n J r).card ≤ 4 * J.card := by
  classical
  calc
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r).card ≤
      ∑ q ∈ J,
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n ((q + r) + r)).card := by
      unfold
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
      exact finset_card_biUnion_le_sum_card J fun q =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n ((q + r) + r)
    _ ≤ ∑ _q ∈ J, 4 := by
      apply Finset.sum_le_sum
      intro q hq
      exact
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_card_le_four
          H latticeSpacing n ((q + r) + r)
    _ = 4 * J.card := by
      simp [Nat.mul_comm]

/-- The complete literal midpoint pair uses at most eight physical Wilson links
per fixed rational slot. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport_card_le
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport
      H latticeSpacing n J r).card ≤ 8 * J.card := by
  classical
  have hLeft :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport_card_le
      H latticeSpacing n J
  have hRight :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport_card_le
      H latticeSpacing n J r
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport
  calc
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J ∪
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r).card ≤
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J).card +
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r).card :=
      Finset.card_union_le _ _
    _ ≤ 4 * J.card + 4 * J.card := Nat.add_le_add hLeft hRight
    _ = 8 * J.card := by omega

end

end MathlibAnalytic
end MGAP4D
