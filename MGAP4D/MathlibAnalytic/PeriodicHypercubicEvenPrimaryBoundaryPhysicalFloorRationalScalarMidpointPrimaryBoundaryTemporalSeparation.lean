import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointPhysicalLinkSeparation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFixedTimeClassification
import Mathlib.Tactic

/-!
# Exact primary-boundary temporal separation of midpoint supports

The preceding support-separation layer proves that admissible reflected-left
and translated-right midpoint supports are disjoint by reflection side.  Here
we retain the actual source-time residues and package the explicit temporal
separation through the primary reflection boundary.

For a reflected-left spatial link with original nonnegative floor step `m`, its
source-time residue is `0` when `m = 0` and `2(H+1)-m` when `m > 0`.  A positive
right link at floor step `p ≤ H` has source-time residue exactly `p`.  We define
the primary-boundary temporal separation to travel from the reflected-left
residue back through time `0` and then out to the right residue.  On the literal
primary scalar plaquette supports this quantity is exactly `m+p`.

The final theorem lifts this identity through the fixed-slot finite unions: any
uniform lower bound on the sum of the two physical floor steps becomes a
uniform lower bound on the primary-boundary temporal separation of every pair
of physical links in the two midpoint supports.

This quantity is an explicit Euclidean temporal separation parameter.  It is
not yet identified with a graph/plaquette-adjacency metric and no covariance
decay, Dobrushin threshold, positive mass, or Hamiltonian gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Temporal separation of two physical positive links measured through the
primary reflection slice.  A left source already on the primary slice
contributes zero; otherwise its backward distance to the primary slice is
`2(H+1) - sourceTime`. -/
def periodicHypercubicEvenPrimaryBoundaryTemporalSeparation
    (H : ℕ)
    (eLeft eRight : PeriodicHypercubicEvenEdge H) : ℕ :=
  if (eLeft.1 0).val = 0 then
    (eRight.1 0).val
  else
    PeriodicHypercubicEvenSideLength H - (eLeft.1 0).val +
      (eRight.1 0).val

/-- If the physical floor step is zero, reflection of a literal primary scalar
plaquette link still has source-time residue zero. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_sourceTime_val_of_floor_zero
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hzero :
      Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) = 0)
    (k : Fin 4) :
    ((periodicHypercubicEvenEdgeReflection H
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k)).1 0).val = 0 := by
  let e :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
      H latticeSpacing n q k
  have hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H := by
    rw [hzero]
    omega
  have hval : (e.1 0).val = 0 := by
    have hsrc :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
        H latticeSpacing n q hwithin k
    simpa [e, hzero] using hsrc
  have hspace : e.2 ≠ 0 := by
    simpa [e] using
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_direction_ne_zero
        H latticeSpacing n q k)
  rw [periodicHypercubicEvenEdgeReflection_spatial H e hspace]
  change (periodicHypercubicEvenTimeReflection H e.1 0).val = 0
  rw [periodicHypercubicEvenTimeReflection_time]
  have ht : e.1 0 = 0 := (ZMod.val_eq_zero _).mp hval
  simp [ht]

/-- For a strictly positive physical floor step `m ≤ H`, reflection sends the
source-time residue of every literal primary scalar plaquette link to
`2(H+1)-m`. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_sourceTime_val_of_floor_positive
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
    ((periodicHypercubicEvenEdgeReflection H
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q k)).1 0).val =
      PeriodicHypercubicEvenSideLength H -
        Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) := by
  let e :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
      H latticeSpacing n q k
  let m : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n)
  have hval : (e.1 0).val = m := by
    simpa [e, m] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
        H latticeSpacing n q hwithin k
  have hspace : e.2 ≠ 0 := by
    simpa [e] using
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_direction_ne_zero
        H latticeSpacing n q k)
  have ht : e.1 0 ≠ 0 := by
    intro hz
    have hzval : (e.1 0).val = 0 := by simp [hz]
    rw [hval] at hzval
    have : 1 ≤ m := by simpa [m] using hpos
    omega
  rw [periodicHypercubicEvenEdgeReflection_spatial H e hspace]
  change (periodicHypercubicEvenTimeReflection H e.1 0).val = _
  rw [periodicHypercubicEvenTimeReflection_time]
  rw [periodicHypercubicEven_neg_val_of_ne_zero H (e.1 0) ht, hval]
  rfl

/-- On a literal reflected-left / positive-right plaquette-edge pair, the
primary-boundary temporal separation is exactly the sum of the two physical
floor steps. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_primaryBoundaryTemporalSeparation_eq_floor_add
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
    periodicHypercubicEvenPrimaryBoundaryTemporalSeparation H
        (periodicHypercubicEvenEdgeReflection H
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n qLeft kLeft))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n qRight kRight) =
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
        Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n) := by
  let mLeft : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n)
  let mRight : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n)
  have hrightVal :
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n qRight kRight).1 0).val = mRight := by
    simpa [mRight] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
        H latticeSpacing n qRight hrightWithin kRight
  by_cases hleftZero : mLeft = 0
  · have hrefVal :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_sourceTime_val_of_floor_zero
        H latticeSpacing n qLeft (by simpa [mLeft] using hleftZero) kLeft
    simp [periodicHypercubicEvenPrimaryBoundaryTemporalSeparation,
      hrefVal, hrightVal, mLeft, mRight, hleftZero]
  · have hleftPos : 1 ≤ mLeft := Nat.one_le_iff_ne_zero.mpr hleftZero
    have hrefVal :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_sourceTime_val_of_floor_positive
        H latticeSpacing n qLeft (by simpa [mLeft] using hleftPos)
        hleftWithin kLeft
    have hrefNe :
        PeriodicHypercubicEvenSideLength H - mLeft ≠ 0 := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    simp only [periodicHypercubicEvenPrimaryBoundaryTemporalSeparation]
    rw [hrefVal, if_neg (by simpa [mLeft] using hrefNe), hrightVal]
    simp only [PeriodicHypercubicEvenSideLength]
    have hmle : mLeft ≤ H := by simpa [mLeft] using hleftWithin
    omega

/-- The exact floor-sum identity holds for arbitrary links chosen from one
reflected-left support and one positive-right support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_primaryBoundaryTemporalSeparation_eq_floor_add
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
    periodicHypercubicEvenPrimaryBoundaryTemporalSeparation H eLeft eRight =
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
        Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((qRight : ℚ) : ℝ) n) := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport,
    Finset.mem_image] at heLeft
  rcases heLeft with ⟨e₀, he₀, rfl⟩
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport,
    Finset.mem_image, Finset.mem_univ, true_and] at he₀ heRight
  rcases he₀ with ⟨kLeft, rfl⟩
  rcases heRight with ⟨kRight, rfl⟩
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_primaryBoundaryTemporalSeparation_eq_floor_add
      H latticeSpacing n qLeft qRight hleftWithin hrightWithin kLeft kRight

/-- A uniform lower bound on all left/right physical-floor sums gives the same
uniform lower bound on the explicit primary-boundary temporal separation of
every physical link pair in the fixed-slot midpoint supports. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_primaryBoundaryTemporalSeparation_ge_of_floor_add_ge
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
        Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
          Int.toNat
            (physicalTemporalFloorStep latticeSpacing
              ((((qRight + r) + r : ℚ) : ℝ)) n))
    (eLeft eRight : PeriodicHypercubicEvenEdge H)
    (heLeft :
      eLeft ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J)
    (heRight :
      eRight ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r) :
    D ≤ periodicHypercubicEvenPrimaryBoundaryTemporalSeparation H eLeft eRight := by
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
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_primaryBoundaryTemporalSeparation_eq_floor_add
      H latticeSpacing n qLeft ((qRight + r) + r)
      (hleftWithin qLeft hqLeft) (hrightWithin qRight hqRight)
      eLeft eRight heLeft heRight]
  exact hfloor qLeft hqLeft qRight hqRight

end

end MathlibAnalytic
end MGAP4D
