import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryIntegerStationarity
import Mathlib.Tactic

/-!
# Lattice-aligned rational covariance of the one-sided primary spatial readout

The physical-floor rational path is indexed by `ℚ`, while each finite Wilson scale is indexed by
natural lattice times obtained from `Int.toNat (floor (q / a_n))`.  Therefore an exact rational
translation statement must account for both the floor carry and the `Int.toNat` truncation.

For a nonnegative rational slot `q`, positive lattice spacing makes its floor step nonnegative.  If
a rational shift `t` is explicitly aligned with a natural lattice step `k`, the floor-arithmetic
receipt from the preceding layers and Lean's `Int.toNat_add_nat` identify the translated natural
index exactly with `k + floorNat(q)`.  The one-sided primary readout covariance can then be applied
without approximation.

This is still a finite-scale pointwise statement.  No stationarity of the whole rational path law,
continuum time-translation invariance, OS contraction, null-space preservation, semigroup,
Hamiltonian, spectral statement, or mass-gap transfer is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A nonnegative rational physical slot has a nonnegative integer floor step whenever the current
lattice spacing is positive. -/
theorem physicalTemporalFloorStep_rational_nonneg
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ physicalTemporalFloorStep latticeSpacing (q : ℝ) n := by
  unfold physicalTemporalFloorStep
  apply Int.floor_nonneg.mpr
  exact div_nonneg (by exact_mod_cast hq) (latticeSpacing_pos n).le

/-- Under natural-step alignment, translating a nonnegative rational slot produces exactly the
corresponding addition of natural lattice indices. -/
theorem physicalTemporalFloorStep_rational_toNat_add_aligned
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (q t : ℚ) (hq : 0 ≤ q)
    (n k : ℕ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ)) :
    Int.toNat
        (physicalTemporalFloorStep latticeSpacing (((q + t : ℚ) : ℝ)) n) =
      k + Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) := by
  have hqfloor :
      0 ≤ physicalTemporalFloorStep latticeSpacing (q : ℝ) n :=
    physicalTemporalFloorStep_rational_nonneg
      latticeSpacing latticeSpacing_pos q hq n
  rw [physicalTemporalFloorStep_rational_add_aligned
    latticeSpacing q t n (k : ℤ) ht]
  simpa [Nat.add_comm] using
    (Int.toNat_add_nat hqfloor k)

/-- Exact future-readout form: at an aligned positive rational shift, the readout of the original
configuration at `q+t` is the readout at `q` of the source translated backward by `k` lattice
steps. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_aligned
    {Gauge : Type} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (q t : ℚ) (hq : 0 ≤ q)
    (k : ℕ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A (q + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) q := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
  rw [physicalTemporalFloorStep_rational_toNat_add_aligned
    latticeSpacing latticeSpacing_pos q t hq n k ht]
  exact
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_eq_neg_configurationTranslation
      H
      (Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n))
      k A

/-- Equivalent forward-source covariance: translating the source by the aligned natural lattice
step and evaluating at `q+t` exactly reproduces the original readout at `q`. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_aligned_configurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (q t : ℚ) (hq : 0 ≤ q)
    (k : ℕ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ) A) (q + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A q := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
  rw [physicalTemporalFloorStep_rational_toNat_add_aligned
    latticeSpacing latticeSpacing_pos q t hq n k ht]
  exact
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_configurationTranslation
      H
      (Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n))
      k A

end

end MathlibAnalytic
end MGAP4D
