import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalTemporalStep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarMidpointCyclicTemporalSeparation
import Mathlib.Tactic

/-!
# Genuine source-time cyclic distance and one-step Wilson locality

The preceding midpoint layer identifies the correct support-specific temporal
quantity on the periodic even time circle.  For path arguments we also need a
metric carrier that is meaningful for arbitrary intermediate physical links.

Here we define the cyclic distance of two source-time residues as the shorter
of their ordinary residue distance and its complementary periodic arc.  This
quantity is symmetric for arbitrary links.  One positive periodic successor
has cyclic distance exactly one, hence every actual Wilson-plaquette-local
pair has source-time cyclic distance at most one.

For the reflected-left / positive-right primary scalar supports, the genuine
cyclic source-time distance agrees exactly with the support-specific cyclic
temporal separation already constructed.  Thus the explicit physical-floor
lower bound transfers to this metric carrier without importing any old graph
metric, Dobrushin threshold, heat-bath time, positive mass, or Hamiltonian gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The shorter periodic distance between two time residues on the even time
circle. -/
def periodicHypercubicEvenTimeCyclicDistance
    (H : ℕ)
    (s t : ZMod (PeriodicHypercubicEvenSideLength H)) : ℕ :=
  let d := Nat.dist s.val t.val
  min d (PeriodicHypercubicEvenSideLength H - d)

/-- Cyclic distance between the source-time residues of two physical links. -/
def periodicHypercubicEvenSourceTimeCyclicDistance
    (H : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) : ℕ :=
  periodicHypercubicEvenTimeCyclicDistance H (e.1 0) (f.1 0)

@[simp]
theorem periodicHypercubicEvenTimeCyclicDistance_self
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenTimeCyclicDistance H t t = 0 := by
  simp [periodicHypercubicEvenTimeCyclicDistance]

/-- Cyclic time distance is symmetric. -/
theorem periodicHypercubicEvenTimeCyclicDistance_comm
    (H : ℕ)
    (s t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenTimeCyclicDistance H s t =
      periodicHypercubicEvenTimeCyclicDistance H t s := by
  simp [periodicHypercubicEvenTimeCyclicDistance, Nat.dist_comm]

/-- Source-time cyclic distance is symmetric. -/
theorem periodicHypercubicEvenSourceTimeCyclicDistance_comm
    (H : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenSourceTimeCyclicDistance H e f =
      periodicHypercubicEvenSourceTimeCyclicDistance H f e := by
  exact periodicHypercubicEvenTimeCyclicDistance_comm H (e.1 0) (f.1 0)

/-- One positive periodic time step has cyclic distance exactly one, including
at the wraparound residue. -/
theorem periodicHypercubicEvenTimeCyclicDistance_add_one_right
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenTimeCyclicDistance H t (t + 1) = 1 := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  unfold periodicHypercubicEvenTimeCyclicDistance
  by_cases hnowrap : t.val + 1 < PeriodicHypercubicEvenSideLength H
  · rw [periodicHypercubicEven_val_add_one_of_lt H t hnowrap]
    have hdist : Nat.dist t.val (t.val + 1) = 1 := by
      rw [Nat.dist_eq_sub_of_le (by omega)]
      omega
    rw [hdist]
    have hle :
        1 ≤ PeriodicHypercubicEvenSideLength H - 1 := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    rw [min_eq_left hle]
  · rw [periodicHypercubicEven_val_add_one_of_not_lt H t hnowrap]
    rw [Nat.dist_zero_right]
    have htlt : t.val < PeriodicHypercubicEvenSideLength H := ZMod.val_lt t
    have hlast : t.val + 1 = PeriodicHypercubicEvenSideLength H := by
      omega
    have hcomp : PeriodicHypercubicEvenSideLength H - t.val = 1 := by
      omega
    have hle : PeriodicHypercubicEvenSideLength H - t.val ≤ t.val := by
      simp only [PeriodicHypercubicEvenSideLength] at hlast htlt ⊢
      omega
    rw [min_eq_right hle, hcomp]

/-- The reverse orientation of one positive periodic step also has distance
one. -/
theorem periodicHypercubicEvenTimeCyclicDistance_add_one_left
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenTimeCyclicDistance H (t + 1) t = 1 := by
  rw [periodicHypercubicEvenTimeCyclicDistance_comm]
  exact periodicHypercubicEvenTimeCyclicDistance_add_one_right H t

/-- The one-unit temporal relation implies cyclic source-time distance at most
one. -/
theorem periodicHypercubicEvenSourceTimeCyclicDistance_le_one_of_temporalUnitRelated
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (h : periodicHypercubicEvenTemporalUnitRelated H e f) :
    periodicHypercubicEvenSourceTimeCyclicDistance H e f ≤ 1 := by
  rcases h with hEq | hSucc | hPred
  · simp [periodicHypercubicEvenSourceTimeCyclicDistance,
      periodicHypercubicEvenTimeCyclicDistance, hEq]
  · have hstep :=
      periodicHypercubicEvenTimeCyclicDistance_add_one_right H (e.1 0)
    simpa [periodicHypercubicEvenSourceTimeCyclicDistance, hSucc] using hstep.le
  · have hstep :=
      periodicHypercubicEvenTimeCyclicDistance_add_one_left H (f.1 0)
    simpa [periodicHypercubicEvenSourceTimeCyclicDistance, hPred] using hstep.le

/-- Every actual Wilson-plaquette-local pair of physical links is at source-time
cyclic distance at most one. -/
theorem periodicHypercubicEvenPlaquetteLocal_sourceTimeCyclicDistance_le_one
    (H : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hlocal : periodicHypercubicEvenPlaquetteLocal H e f) :
    periodicHypercubicEvenSourceTimeCyclicDistance H e f ≤ 1 := by
  exact
    periodicHypercubicEvenSourceTimeCyclicDistance_le_one_of_temporalUnitRelated H
      (periodicHypercubicEvenPlaquetteLocal_temporalUnitRelated H hlocal)

/-- On literal reflected-left / positive-right primary scalar plaquette links,
the genuine source-time cyclic distance is exactly the explicit cyclic
physical-floor formula. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTimeCyclicDistance_eq_min_floor_add_complement
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
    periodicHypercubicEvenSourceTimeCyclicDistance H
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
  · have hrefVal :
        ((periodicHypercubicEvenEdgeReflection H
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n qLeft kLeft)).1 0).val = 0 :=
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_sourceTime_val_of_floor_zero
        H latticeSpacing n qLeft (by simpa [mLeft] using hleftZero) kLeft
    simp only [periodicHypercubicEvenSourceTimeCyclicDistance,
      periodicHypercubicEvenTimeCyclicDistance]
    rw [hrefVal, hrightVal, Nat.dist_zero_left]
    change
      min mRight (PeriodicHypercubicEvenSideLength H - mRight) =
        min (mLeft + mRight)
          (PeriodicHypercubicEvenSideLength H - (mLeft + mRight))
    simp [hleftZero]
  · have hleftPos : 1 ≤ mLeft := Nat.one_le_iff_ne_zero.mpr hleftZero
    have hrefVal :
        ((periodicHypercubicEvenEdgeReflection H
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n qLeft kLeft)).1 0).val =
          PeriodicHypercubicEvenSideLength H - mLeft := by
      simpa [mLeft] using
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdgeReflection_sourceTime_val_of_floor_positive
          H latticeSpacing n qLeft (by simpa [mLeft] using hleftPos)
          hleftWithin kLeft
    have hmLeftLe : mLeft ≤ H := by
      simpa [mLeft] using hleftWithin
    have hmRightLe : mRight ≤ H := by
      simpa [mRight] using hrightWithin
    have hrightLe :
        mRight ≤ PeriodicHypercubicEvenSideLength H - mLeft := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    simp only [periodicHypercubicEvenSourceTimeCyclicDistance,
      periodicHypercubicEvenTimeCyclicDistance]
    rw [hrefVal, hrightVal, Nat.dist_eq_sub_of_le_right hrightLe]
    have hsub :
        (PeriodicHypercubicEvenSideLength H - mLeft) - mRight =
          PeriodicHypercubicEvenSideLength H - (mLeft + mRight) := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    rw [hsub]
    have hsumLe :
        mLeft + mRight ≤ PeriodicHypercubicEvenSideLength H := by
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    have hdoubleSub :
        PeriodicHypercubicEvenSideLength H -
            (PeriodicHypercubicEvenSideLength H - (mLeft + mRight)) =
          mLeft + mRight := by
      omega
    rw [hdoubleSub]
    change
      min (PeriodicHypercubicEvenSideLength H - (mLeft + mRight))
          (mLeft + mRight) =
        min (mLeft + mRight)
          (PeriodicHypercubicEvenSideLength H - (mLeft + mRight))
    exact min_comm _ _

/-- On literal midpoint links, the genuine cyclic source-time metric equals the
support-specific cyclic separation from the preceding layer. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTimeCyclicDistance_eq_cyclicTemporalSeparation
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
    periodicHypercubicEvenSourceTimeCyclicDistance H
        (periodicHypercubicEvenEdgeReflection H
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n qLeft kLeft))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n qRight kRight) =
      periodicHypercubicEvenCyclicTemporalSeparation H
        (periodicHypercubicEvenEdgeReflection H
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n qLeft kLeft))
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n qRight kRight) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTimeCyclicDistance_eq_min_floor_add_complement
      H latticeSpacing n qLeft qRight hleftWithin hrightWithin kLeft kRight,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_cyclicTemporalSeparation_eq_min_floor_add_complement
      H latticeSpacing n qLeft qRight hleftWithin hrightWithin kLeft kRight]

/-- The genuine cyclic source-time metric and the preceding support-specific
cyclic separation agree for arbitrary physical links in one reflected-left and
one positive-right scalar support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_sourceTimeCyclicDistance_eq_cyclicTemporalSeparation
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
    periodicHypercubicEvenSourceTimeCyclicDistance H eLeft eRight =
      periodicHypercubicEvenCyclicTemporalSeparation H eLeft eRight := by
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
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTimeCyclicDistance_eq_cyclicTemporalSeparation
      H latticeSpacing n qLeft qRight hleftWithin hrightWithin kLeft kRight

/-- The same equality lifts through the fixed-slot midpoint finite unions. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_sourceTimeCyclicDistance_eq_cyclicTemporalSeparation
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H)
    (eLeft eRight : PeriodicHypercubicEvenEdge H)
    (heLeft :
      eLeft ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J)
    (heRight :
      eRight ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r) :
    periodicHypercubicEvenSourceTimeCyclicDistance H eLeft eRight =
      periodicHypercubicEvenCyclicTemporalSeparation H eLeft eRight := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport,
    Finset.mem_biUnion] at heLeft
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport,
    Finset.mem_biUnion] at heRight
  rcases heLeft with ⟨qLeft, hqLeft, heLeft⟩
  rcases heRight with ⟨qRight, hqRight, heRight⟩
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupports_sourceTimeCyclicDistance_eq_cyclicTemporalSeparation
      H latticeSpacing n qLeft ((qRight + r) + r)
      (hleftWithin qLeft hqLeft) (hrightWithin qRight hqRight)
      eLeft eRight heLeft heRight

/-- Any uniform lower bound on the explicit cyclic floor formula therefore
transfers to the genuine cyclic source-time metric on every fixed-slot
midpoint support pair. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_sourceTimeCyclicDistance_ge_of_floor_min_ge
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
    D ≤ periodicHypercubicEvenSourceTimeCyclicDistance H eLeft eRight := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_sourceTimeCyclicDistance_eq_cyclicTemporalSeparation
      H latticeSpacing n J r hleftWithin hrightWithin eLeft eRight heLeft heRight]
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_cyclicTemporalSeparation_ge_of_floor_min_ge
      H latticeSpacing n J r D hleftWithin hrightWithin hfloor
      eLeft eRight heLeft heRight

end

end MathlibAnalytic
end MGAP4D
