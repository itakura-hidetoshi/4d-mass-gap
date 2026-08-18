import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalAlignedCylinderStationarity
import Mathlib.Tactic

/-!
# Carry-resolved rational-time covariance of the one-sided primary readout

Exact lattice alignment is sufficient for finite rational stationarity, but a fixed rational shift
need not be an integer multiple of the lattice spacing at every finite scale.  The universal floor
arithmetic from the preceding layers shows that this failure is nevertheless completely rigid: for
nonnegative rational times the translated natural lattice index differs from the sum of the two
natural floor indices by exactly zero or one.

This file pushes that statement through the actual one-sided primary Wilson readout.  After removing
the common integer source translation selected by the shift `t`, every coordinate at `q+t` is
exactly either the baseline coordinate at `q` or the coordinate one lattice step later.  Thus the
remaining obstruction to generic continuum rational-time stationarity is isolated to control of a
single adjacent lattice-time step.

No adjacent-step regularity estimate, continuum stationarity, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is assumed or
asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The common natural lattice shift selected by a rational physical time at one finite scale. -/
def physicalTemporalFloorRationalCommonNatShift
    (latticeSpacing : ℕ → ℝ) (t : ℚ) (n : ℕ) : ℕ :=
  Int.toNat (physicalTemporalFloorStep latticeSpacing (t : ℝ) n)

/-- For nonnegative rational `q,t`, the natural floor index of `q+t` is exactly the sum of the
natural floor indices, with a possible single carry. -/
theorem physicalTemporalFloorStep_rational_toNat_add_eq_or_eq_add_one
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (q t : ℚ) (hq : 0 ≤ q) (ht : 0 ≤ t) (n : ℕ) :
    Int.toNat
        (physicalTemporalFloorStep latticeSpacing (((q + t : ℚ) : ℝ)) n) =
        Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) +
          physicalTemporalFloorRationalCommonNatShift latticeSpacing t n ∨
      Int.toNat
        (physicalTemporalFloorStep latticeSpacing (((q + t : ℚ) : ℝ)) n) =
        Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) +
          physicalTemporalFloorRationalCommonNatShift latticeSpacing t n + 1 := by
  have hqfloor :
      0 ≤ physicalTemporalFloorStep latticeSpacing (q : ℝ) n :=
    physicalTemporalFloorStep_rational_nonneg
      latticeSpacing latticeSpacing_pos q hq n
  have htfloor :
      0 ≤ physicalTemporalFloorStep latticeSpacing (t : ℝ) n :=
    physicalTemporalFloorStep_rational_nonneg
      latticeSpacing latticeSpacing_pos t ht n
  rcases
      physicalTemporalFloorStep_rational_add_eq_or_eq_add_one
        latticeSpacing q t n with hcarry | hcarry
  · left
    rw [hcarry, Int.toNat_add hqfloor htfloor]
    rfl
  · right
    rw [hcarry]
    have hsum :
        0 ≤ physicalTemporalFloorStep latticeSpacing (q : ℝ) n +
          physicalTemporalFloorStep latticeSpacing (t : ℝ) n :=
      add_nonneg hqfloor htfloor
    rw [Int.toNat_add hsum (by norm_num : (0 : ℤ) ≤ 1)]
    rw [Int.toNat_add hqfloor htfloor]
    rfl

/-- The one-lattice-step future of a rational primary readout coordinate.  This is deliberately
kept as an exact finite-scale object rather than identified with any continuum derivative. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalOneStepReadout
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (q : ℚ) :
    PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge :=
  periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H
    (Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) + 1) A

/-- After removing the common natural lattice translation associated with `t`, every nonnegative
rational coordinate at `q+t` is exactly either the baseline `q` coordinate or its one-step future. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_carry_resolved
    {Gauge : Type} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (q t : ℚ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A (q + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H)
          (-(physicalTemporalFloorRationalCommonNatShift latticeSpacing t n : ℤ)) A) q ∨
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A (q + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalOneStepReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H)
          (-(physicalTemporalFloorRationalCommonNatShift latticeSpacing t n : ℤ)) A) q := by
  have hnat :=
    physicalTemporalFloorStep_rational_toNat_add_eq_or_eq_add_one
      latticeSpacing latticeSpacing_pos q t hq ht n
  rcases hnat with hzero | hone
  · left
    unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
    rw [hzero]
    have hcov :=
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_eq_neg_configurationTranslation
        H
        (Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n))
        (physicalTemporalFloorRationalCommonNatShift latticeSpacing t n) A
    convert hcov using 1 <;> omega
  · right
    unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
    unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalOneStepReadout
    rw [hone]
    have hcov :=
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_add_eq_neg_configurationTranslation
        H
        (Int.toNat (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) + 1)
        (physicalTemporalFloorRationalCommonNatShift latticeSpacing t n) A
    convert hcov using 1 <;> omega

/-- Finite-slot form of the same carry resolution.  Every coordinate of the shifted joint readout
is, after one common inverse source translation, either its unshifted coordinate or exactly one
lattice step later. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_carry_resolved
    {Gauge : Type} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    ∀ q : J,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
          H latticeSpacing n J t A q =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          H latticeSpacing n J
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (PeriodicHypercubicEvenSideLength H)
            (-(physicalTemporalFloorRationalCommonNatShift latticeSpacing t n : ℤ)) A) q ∨
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
          H latticeSpacing n J t A q =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalOneStepReadout
          H latticeSpacing n
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (PeriodicHypercubicEvenSideLength H)
            (-(physicalTemporalFloorRationalCommonNatShift latticeSpacing t n : ℤ)) A) q.1 := by
  intro q
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A (q.1 + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H)
          (-(physicalTemporalFloorRationalCommonNatShift latticeSpacing t n : ℤ)) A) q.1 ∨
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A (q.1 + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalOneStepReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H)
          (-(physicalTemporalFloorRationalCommonNatShift latticeSpacing t n : ℤ)) A) q.1
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_carry_resolved
      H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) ht A

end

end MathlibAnalytic
end MGAP4D
