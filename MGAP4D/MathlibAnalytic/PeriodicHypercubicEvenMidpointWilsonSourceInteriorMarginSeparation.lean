import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceSeparatedCovariance
import Mathlib.Tactic

/-!
# Interior-margin criterion for midpoint Wilson-source separation

The preceding layer attaches the actual static midpoint Wilson covariance to its
literal reflected-left and translated-right physical-link supports.  Its
separation theorem is naturally stated using the shorter cyclic distance

`min (mLeft + mRight) (2 * (H + 1) - (mLeft + mRight))`.

For scaling arguments it is more convenient to replace this cyclic minimum by
three transparent one-sided inequalities.  If

* `D <= mLeft + mRight`,
* `mLeft + D <= H`, and
* `mRight + D <= H`,

then the direct arc is at least `D` and both endpoints lie far enough inside the
primary half extent that the complementary periodic arc is also at least `D`.
This file proves that arithmetic receipt and feeds it directly into the actual
Wilson-source covariance support theorem.

This remains finite support geometry.  It proves no covariance decay rate and
introduces no high-temperature Dobrushin condition, stochastic-time/Euclidean-
time identification, positive mass, or Hamiltonian gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Direct floor-sum separation plus a `D`-step interior margin on each side
implies the cyclic physical-floor separation lower bound used by the actual
plaquette-local path geometry. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_floor_min_ge_of_sum_ge_of_interior_margin
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (D : ℕ)
    (hsum : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
          Int.toNat
            (physicalTemporalFloorStep latticeSpacing
              ((((qRight + r) + r : ℚ) : ℝ)) n))
    (hleftMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) + D ≤ H)
    (hrightMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) + D ≤ H) :
    ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
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
                  ((((qRight + r) + r : ℚ) : ℝ)) n))) := by
  intro qLeft hqLeft qRight hqRight
  let mLeft : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n)
  let mRight : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((((qRight + r) + r : ℚ) : ℝ)) n)
  have hsum' : D ≤ mLeft + mRight := by
    simpa [mLeft, mRight] using hsum qLeft hqLeft qRight hqRight
  have hleft' : mLeft + D ≤ H := by
    simpa [mLeft] using hleftMargin qLeft hqLeft
  have hright' : mRight + D ≤ H := by
    simpa [mRight] using hrightMargin qRight hqRight
  have hcomp :
      D ≤ PeriodicHypercubicEvenSideLength H - (mLeft + mRight) := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  exact le_min hsum' hcomp

/-- The same interior margins automatically imply the per-slot half-extent
admissibility required by the literal support geometry. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_within_of_interior_margin
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (D : ℕ)
    (hleftMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) + D ≤ H)
    (hrightMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) + D ≤ H) :
    (∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H) ∧
    (∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H) := by
  constructor
  · intro q hq
    have h := hleftMargin q hq
    omega
  · intro q hq
    have h := hrightMargin q hq
    omega

/-- Interior floor margins are sufficient to produce the actual
Wilson-plaquette-local support separation of the midpoint pair. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_plaquetteLocalSeparatedBy_of_sum_ge_of_interior_margin
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (D : ℕ)
    (hsum : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
          Int.toNat
            (physicalTemporalFloorStep latticeSpacing
              ((((qRight + r) + r : ℚ) : ℝ)) n))
    (hleftMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) + D ≤ H)
    (hrightMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) + D ≤ H) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r) := by
  have hwithin :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_within_of_interior_margin
      H latticeSpacing n J r D hleftMargin hrightMargin
  have hfloor :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_floor_min_ge_of_sum_ge_of_interior_margin
      H latticeSpacing n J r D hsum hleftMargin hrightMargin
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_plaquetteLocalSeparatedBy_of_floor_min_ge
      H latticeSpacing n J r D hwithin.1 hwithin.2 hfloor

/-- For the literal ordinary static midpoint Wilson covariance, the same three
interior inequalities simultaneously give exact left support dependence, exact
right support dependence, and actual `D`-step plaquette-local support
separation. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_support_receipt_of_sum_ge_of_interior_margin
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (D : ℕ)
    (hsum : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
          Int.toNat
            (physicalTemporalFloorStep latticeSpacing
              ((((qRight + r) + r : ℚ) : ℝ)) n))
    (hleftMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) + D ≤ H)
    (hrightMargin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) + D ≤ H)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    (∀ A B : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ,
      (∀ e,
        e ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
            H latticeSpacing n J →
        A e = B e) →
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
          H N latticeSpacing n J F A =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
          H N latticeSpacing n J F B) ∧
    (∀ A B : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ,
      (∀ e,
        e ∈
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
            H latticeSpacing n J r →
        A e = B e) →
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
          H N latticeSpacing n J r F A =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
          H N latticeSpacing n J r F B) ∧
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r) := by
  have hwithin :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_within_of_interior_margin
      H latticeSpacing n J r D hleftMargin hrightMargin
  have hfloor :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_floor_min_ge_of_sum_ge_of_interior_margin
      H latticeSpacing n J r D hsum hleftMargin hrightMargin
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_support_receipt_of_floor_min_ge
      H N latticeSpacing n J hJ r hr D hwithin.1 hwithin.2 hfloor F

end

end MathlibAnalytic
end MGAP4D
