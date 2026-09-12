import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointPrimaryBoundaryTemporalSeparation
import Mathlib.Tactic

/-!
# Cyclic temporal separation of midpoint physical-link supports

The primary-boundary separation layer records the Euclidean-time arc through
the primary reflection slice.  On the periodic even time circle there is also
the complementary arc through the secondary wraparound boundary.  Therefore
an unrestricted local path cannot in general be bounded below by the primary
arc alone.

Here we package the correct periodic temporal separation as the minimum of the
primary arc and its complementary arc.  On the literal reflected-left and
positive-right scalar plaquette links this is exactly

`min (mLeft + mRight) (2 * (H + 1) - (mLeft + mRight))`.

The fixed-slot theorem lifts any uniform lower bound on this explicit cyclic
quantity to every pair of actual physical links in the two midpoint supports.

This is still temporal geometry, not yet the plaquette-local path-length
lower bound.  No covariance decay, small-coupling condition, positive mass,
or Hamiltonian gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Periodic temporal separation between a reflected-left and positive-right
physical link: the shorter of the primary-boundary arc and its complementary
arc around the even periodic time circle. -/
def periodicHypercubicEvenCyclicTemporalSeparation
    (H : ℕ)
    (eLeft eRight : PeriodicHypercubicEvenEdge H) : ℕ :=
  let d := periodicHypercubicEvenPrimaryBoundaryTemporalSeparation H eLeft eRight
  min d (PeriodicHypercubicEvenSideLength H - d)

/-- On literal reflected-left / positive-right primary scalar plaquette links,
the cyclic temporal separation is exactly the minimum of the physical-floor
sum and its complementary periodic arc. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_cyclicTemporalSeparation_eq_min_floor_add_complement
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (qLeft qRight : ℚ)
    (hleftWithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) ≤ H)
    (hrightWithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n) ≤ H)
    (kLeft kRight : Fin 4) :
    periodicHypercubicEvenCyclicTemporalSeparation H
        (periodicHypercubicEvenEdgeReflection H
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n qLeft kLeft))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n qRight kRight) =
      min
        (Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
          Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n))
        (PeriodicHypercubicEvenSideLength H -
          (Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n))) := by
  simp only [periodicHypercubicEvenCyclicTemporalSeparation]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_primaryBoundaryTemporalSeparation_eq_floor_add
      H latticeSpacing n qLeft qRight hleftWithin hrightWithin kLeft kRight]

/-- The same exact cyclic-floor formula holds for arbitrary physical links
chosen from one reflected-left and one positive-right scalar plaquette
support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_cyclicTemporalSeparation_eq_min_floor_add_complement
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (qLeft qRight : ℚ)
    (hleftWithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) ≤ H)
    (hrightWithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n) ≤ H)
    (eLeft eRight : PeriodicHypercubicEvenEdge H)
    (heLeft :
      eLeft ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n qLeft)
    (heRight :
      eRight ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n qRight) :
    periodicHypercubicEvenCyclicTemporalSeparation H eLeft eRight =
      min
        (Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
          Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n))
        (PeriodicHypercubicEvenSideLength H -
          (Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n))) := by
  simp only [periodicHypercubicEvenCyclicTemporalSeparation]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_primaryBoundaryTemporalSeparation_eq_floor_add
      H latticeSpacing n qLeft qRight hleftWithin hrightWithin
      eLeft eRight heLeft heRight]

/-- A uniform lower bound on the explicit cyclic floor separation gives the
same lower bound for every physical-link pair in the fixed-slot midpoint
supports. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_cyclicTemporalSeparation_ge_of_floor_min_ge
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (D : ℕ)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H)
    (hfloor : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        min
          (Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing
                ((((qRight + r) + r : ℚ) : ℝ)) n))
          (PeriodicHypercubicEvenSideLength H -
            (Int.toNat
                (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
              Int.toNat
                (physicalTemporalFloorStep latticeSpacing
                  ((((qRight + r) + r : ℚ) : ℝ)) n))))
    (eLeft eRight : PeriodicHypercubicEvenEdge H)
    (heLeft :
      eLeft ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J)
    (heRight :
      eRight ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r) :
    D ≤ periodicHypercubicEvenCyclicTemporalSeparation H eLeft eRight := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport,
    Finset.mem_biUnion] at heLeft
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport,
    Finset.mem_biUnion] at heRight
  rcases heLeft with ⟨qLeft, hqLeft, heLeft⟩
  rcases heRight with ⟨qRight, hqRight, heRight⟩
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_cyclicTemporalSeparation_eq_min_floor_add_complement
      H latticeSpacing n qLeft ((qRight + r) + r)
      (hleftWithin qLeft hqLeft) (hrightWithin qRight hqRight)
      eLeft eRight heLeft heRight]
  exact hfloor qLeft hqLeft qRight hqRight

end

end MathlibAnalytic
end MGAP4D
