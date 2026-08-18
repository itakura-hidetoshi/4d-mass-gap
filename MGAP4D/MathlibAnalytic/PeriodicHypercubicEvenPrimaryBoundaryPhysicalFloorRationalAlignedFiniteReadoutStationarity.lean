import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalAlignedReadoutCovariance
import Mathlib.Tactic

/-!
# Aligned finite rational readout stationarity for the one-sided primary Wilson law

For a fixed finite nonnegative slot set `J`, it is cleaner to keep the original index type and
regard a rational shift `t` as the joint readout

`q ↦ R(q+t,A)`,  `q : J`.

This avoids pretending that the translated finite set `J+t` is definitionally the same subtype as
`J`.  Under an explicit natural lattice-step alignment receipt, the preceding pointwise theorem
identifies this shifted joint readout with the unshifted joint readout of the inverse-translated
Wilson source.  Exact integer temporal invariance of the same finite Wilson Gibbs law then gives
stationarity of the joint pushforward law.

No whole-path rational stationarity, continuum time-translation invariance, OS contraction,
null-space preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is
asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

/-- Joint finite-slot primary readout after shifting every selected rational time by `t`, while
retaining the original finite index type `J`. -/
def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
    {Gauge : Type*}
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (t : ℚ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    ∀ q : J, PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge :=
  fun q =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
      H latticeSpacing n A (q.1 + t)

/-- The shifted finite rational readout is measurable for every measurable value space. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (t : ℚ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
        (Gauge := Gauge) H latticeSpacing n J t) := by
  apply measurable_pi_lambda
  intro q
  simpa [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout] using
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_measurable
      (Gauge := Gauge) H
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing (((q.1 + t : ℚ) : ℝ)) n)))

/-- Under explicit natural-step alignment, the shifted finite nonnegative readout is exactly the
ordinary finite readout of the source translated backward by the aligned integer step. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_aligned
    {Gauge : Type} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ)
    (k : ℕ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
        H latticeSpacing n J t A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) := by
  funext q
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A (q.1 + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) q.1
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_aligned
      H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) k ht A

/-- Equivalent forward-source form of aligned finite-slot covariance. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_aligned_configurationTranslation
    {Gauge : Type} [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ)
    (k : ℕ)
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
        H latticeSpacing n J t
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ) A) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        H latticeSpacing n J A := by
  funext q
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ) A) (q.1 + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
        H latticeSpacing n A q.1
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_aligned_configurationTranslation
      H latticeSpacing latticeSpacing_pos n q.1 t (hJ q) k ht A

local instance primaryAlignedFiniteStationarityIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryAlignedFiniteStationarityCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance primaryAlignedFiniteStationaritySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryAlignedFiniteStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryAlignedFiniteStationarityBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- At every explicitly aligned positive rational shift, the shifted joint finite nonnegative
primary readout has exactly the same finite Wilson Gibbs pushforward law as the unshifted readout. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_wilsonGibbs_law_stationary_aligned
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
    (ht : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ)) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := by
    refine ⟨?_⟩
    simp [PeriodicHypercubicEvenSideLength]
  let T :=
    periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))
  have hT : Measurable T :=
    (periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ))).measurable
  have hR : Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        H latticeSpacing n J) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout_measurable
      H latticeSpacing n J
  have hcov :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J t =
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J) ∘ T := by
    funext A
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalShiftedReadout_aligned
        H latticeSpacing latticeSpacing_pos n J hJ t k ht A
  rw [hcov]
  calc
    Measure.map
        ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J) ∘ T)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J)
        (Measure.map T
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      (Measure.map_map hR hT).symm
    _ = Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n J)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      exact congrArg
        (Measure.map
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n J))
        (periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta (-(k : ℤ)))

end

end MathlibAnalytic
end MGAP4D
