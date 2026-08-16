import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftAction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathLaw

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalExactShiftNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalExactShiftTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalExactShiftCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalExactShiftSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalExactShiftMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalExactShiftBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Read only rational coordinates from a real-indexed scalar path. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
    (x : ℝ → ℝ) : ℚ → ℝ :=
  fun q => x (q : ℝ)

/-- Rational restriction is measurable for the product Borel structures. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction_measurable :
    Measurable
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction := by
  exact measurable_pi_lambda _ (fun q => measurable_pi_apply (q : ℝ))

/-- Restricting a real path after a rational real-time translation is exactly
rational path translation after restriction. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction_realShift
    (r : ℚ) (x : ℝ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
          (r : ℝ) x) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction x) := by
  funext q
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift]

/-- The direct same-Wilson-source rational floor path law is precisely the
rational-coordinate restriction of the already constructed real floor path
law.

This is a deterministic pushforward identity; no independence or extra
Kolmogorov extension is introduced. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_eq_map_rationalRestriction_realPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
  symm
  calc
    Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
          (Measure.map
            (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
              H N hN beta hbeta)
            (periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure)) =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
      Measure.map_map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction_measurable
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
          latticeSpacing n)
    _ = Measure.map
        ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction ∘
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
              latticeSpacing n) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      Measure.map_map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction_measurable.comp
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
            latticeSpacing n))
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
          H N hN beta hbeta)
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
          H N hN beta hbeta latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure)
      funext A
      rfl

/-- At any finite scale where a rational translation is an exact lattice-time
multiple, the full rational floor path law is exactly stationary.

The proof is inherited functorially from the real floor path lattice-subgroup
stationarity.  It preserves every rational-time joint correlation at once. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_map_exactLatticeShift_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (r : ℚ) (k : ℤ)
    (hr : (r : ℝ) = (k : ℝ) * latticeSpacing n) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  have hRestriction :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction_measurable
  have hRationalShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r
  have hRealShift :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_measurable (r : ℝ)
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_eq_map_rationalRestriction_realPathMeasure]
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
        (Measure.map
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
            H N hN beta hbeta latticeSpacing n)) =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) :=
      Measure.map_map hRationalShift hRestriction
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift (r : ℝ))
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) := by
      apply congrArg (fun f => Measure.map f
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n))
      funext x
      exact
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction_realShift
          r x).symm
    _ = Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift (r : ℝ))
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
            H N hN beta hbeta latticeSpacing n)) :=
      (Measure.map_map hRestriction hRealShift).symm
    _ = Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalRestriction
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) := by
      rw [hr]
      rw [
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_map_latticeShift_eq_self
          H N hN beta hbeta latticeSpacing latticeSpacing_pos n k]

/-- Probability-measure form of exact finite-scale rational path stationarity. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_map_exactLatticeShift_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (r : ℚ) (k : ℤ)
    (hr : (r : ℝ) = (k : ℝ) * latticeSpacing n) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n).map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [ProbabilityMeasure.toMeasure_map,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_toMeasure] using
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_map_exactLatticeShift_eq_self
      H N hN beta hbeta latticeSpacing latticeSpacing_pos n r k hr

end

end MathlibAnalytic
end MGAP4D
