import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalAlignedFiniteReadoutStationarity
import Mathlib.Tactic

/-!
# Aligned rational cylinder stationarity for the one-sided primary Wilson law

The preceding layer proves equality of the shifted and unshifted finite joint primary readout laws
under an explicit natural lattice-step alignment receipt.  This file pushes that equality through
an arbitrary measurable real cylinder on the same finite coordinate carrier.

Thus every measurable finite nonnegative primary-boundary cylinder has the same finite Wilson
pushforward law after an aligned rational time shift.  The result is still a finite-scale theorem;
it does not assert whole-path or continuum rational-time stationarity.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

/-- A real cylinder obtained by applying `g` to the finite primary readout with every selected
rational slot shifted by `t`. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedCylinder
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (t : ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : ℝ :=
  g (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
    H latticeSpacing n J t A)

/-- Measurability of the shifted cylinder follows from measurability of its finite coordinate map. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedCylinder_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (t : ℚ)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedCylinder
        H latticeSpacing n J t g) :=
  hg.comp
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_measurable
      (Gauge := Gauge) H latticeSpacing n J t)

local instance primaryAlignedCylinderStationarityIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryAlignedCylinderStationarityCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance primaryAlignedCylinderStationaritySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryAlignedCylinderStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryAlignedCylinderStationarityBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- Every measurable finite nonnegative primary cylinder has exactly the same real pushforward law
after an explicitly aligned rational shift. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedCylinder_wilsonGibbs_law_stationary_aligned
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ)
    (k : ℕ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedCylinder
          H latticeSpacing n J t g)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalCylinder
          H latticeSpacing n J g)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have hShift : Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        H latticeSpacing n J t) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_measurable
      H latticeSpacing n J t
  have hBase : Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        H latticeSpacing n J) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_measurable
      H latticeSpacing n J
  have hLaw :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_wilsonGibbs_law_stationary_aligned
      H N hN beta hbeta latticeSpacing latticeSpacing_pos n J hJ t k ht
  change
    Measure.map
        (g ∘
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (g ∘
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  calc
    Measure.map
        (g ∘
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map g
        (Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J t)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      (Measure.map_map hg hShift).symm
    _ = Measure.map g
        (Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      congrArg (Measure.map g) hLaw
    _ = Measure.map
        (g ∘
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      Measure.map_map hg hBase

end

end MathlibAnalytic
end MGAP4D
