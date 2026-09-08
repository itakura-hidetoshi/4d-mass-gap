import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The genuine ground-state Wilson joint law is absolutely continuous with
respect to the spatial pair-Haar reference measure because it is defined by an
explicit density on that reference carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta ≪
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
  exact withDensity_absolutelyContinuous _ _

/-- Strict positivity of the normalized Wilson ground-state density gives the
reverse absolute-continuity direction: pair Haar has no null set beyond those
of the genuine joint law.  No uniform density lower bound is used. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N ≪
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let w :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ENNReal :=
    fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z)
  have hw : AEMeasurable w μ := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hw_ne_zero : ∀ᵐ z ∂μ, w z ≠ 0 := by
    filter_upwards
      [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
        H N hN beta hbeta] with z hz
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hz)
  have hμ := withDensity_absolutelyContinuous' hw hw_ne_zero
  simpa [μ, w,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure] using hμ

/-- The actual Wilson ground-state joint law and pair Haar therefore have the
same measure-zero geometry.  This is the transport surface for the upcoming
common-fixed-space identification; it does not assert any two-sided `L²` norm
comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_mutuallyAbsolutelyContinuous_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta ≪
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) ∧
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N ≪
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
      H N hN beta hbeta⟩

end

end MathlibAnalytic
end MGAP4D
