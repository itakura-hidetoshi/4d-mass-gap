import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding

/-!
# Rational restriction of the finite real floor path law

The finite real-indexed floor path and the rational floor skeleton are not two
independent constructions.  They are deterministic readouts of the same actual
finite Wilson configuration using the same physical floor selector.

This file makes that same-root relation explicit.  Restricting a real floor path
to rational times is continuous and measurable, agrees pointwise with the
rational floor readout, and pushes the full finite real floor path law exactly
to the already used rational path law.

No continuum real-path law, path continuity, or real-time stationarity is
asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRealPathRationalRestrictionNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRealPathRationalRestrictionTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRealPathRationalRestrictionCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRealPathRationalRestrictionSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRealPathRationalRestrictionMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRealPathRationalRestrictionBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Restrict a real-indexed scalar path to its rational-time skeleton. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational
    (x : ℝ → ℝ) : ℚ → ℝ :=
  fun q => x (q : ℝ)

/-- Rational restriction is continuous for the product topologies. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_continuous :
    Continuous
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational := by
  exact continuous_pi (fun q => continuous_apply (q : ℝ))

/-- Hence rational restriction is measurable for the product Borel sigma algebras. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_measurable :
    Measurable
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational :=
  periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_continuous.measurable

/-- Restricting the real floor extension of one integer path gives the same
floor selector on every rational time. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_floorExtension
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (x : ℤ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n x) =
      fun q : ℚ => x (physicalTemporalFloorStep latticeSpacing (q : ℝ) n) := by
  rfl

/-- Same-root pointwise compatibility: the real floor path of one Wilson
configuration, restricted to rational times, is exactly the rational floor
readout of that same configuration. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_floorExtension_temporalPathReadout_eq_rationalPathReadout
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta A)) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n A := by
  rfl

/-- The finite real floor path law pushes forward under rational restriction to
exactly the finite rational floor path law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_map_restrictRational_eq_rationalPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure
  calc
    Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
            H N hN beta hbeta)) =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
            latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
          H N hN beta hbeta) :=
      Measure.map_map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_measurable
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
          latticeSpacing n)
    _ = Measure.map
        ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational ∘
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
              latticeSpacing n) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout
            H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      unfold periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure
      exact
        Measure.map_map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_measurable.comp
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension_measurable
              latticeSpacing n))
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathReadout_measurable
            H N hN beta hbeta)
    _ = periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
        H N hN beta hbeta latticeSpacing n := by
      unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure
      apply congrArg
        (fun f => Measure.map f
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure)
      funext A
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_floorExtension_temporalPathReadout_eq_rationalPathReadout
          H N hN beta hbeta latticeSpacing n A

/-- Probability-measure form of the same exact finite-scale compatibility. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure_map_restrictRational_eq_rationalPathProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n).map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_measurable.aemeasurable =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure_toMeasure]
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_toMeasure]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathMeasure_map_restrictRational_eq_rationalPathMeasure
      H N hN beta hbeta latticeSpacing n

/-- The rational physical embedding used for Prokhorov extraction is exactly
the rational restriction of the finite real floor path probability law at every
scale.  This is the bridge needed for any future real-path continuum lifting. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq_realPath_map_restrictRational
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure n =
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure
        (H n) N hN (beta n) (hbeta n) latticeSpacing n).map
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathRestrictRational_measurable.aemeasurable := by
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop n]
  exact
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathProbabilityMeasure_map_restrictRational_eq_rationalPathProbabilityMeasure
      (H n) N hN (beta n) (hbeta n) latticeSpacing n).symm

end
end MathlibAnalytic
end MGAP4D
