import MGAP4D.MathlibAnalytic.PeriodicHypercubicTranslationInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPhysicalEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedTemporalSymmetryLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance periodicTemporalIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance periodicTemporalCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance periodicTemporalSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance periodicTemporalMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance periodicTemporalBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- Construct the physical temporal-action package for the canonical periodic
`SU(N)` Wilson embedding from a physical real-parameter translation action and
scale-dependent periodic lattice displacements.

Finite-volume Gibbs invariance is no longer supplied as an assumption.  It is
generated automatically by periodic coordinate translation invariance. -/
noncomputable def periodicHypercubicSpecialUnitaryPhysicalTemporalAction
    {PhysicalConfiguration : Type}
    [TopologicalSpace PhysicalConfiguration] [MeasurableSpace PhysicalConfiguration]
    [BorelSpace PhysicalConfiguration] [PolishSpace PhysicalConfiguration]
    (sideLength : ℕ → ℕ) (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (beta_nonneg : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n,
      (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
        (sideLength n) N (sideLength_pos n) hN
        (beta n) (beta_nonneg n)).base.Configuration →
        PhysicalConfiguration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (latticeSpacing : ℕ → ℝ) (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (physicalTranslate : ℝ → Homeomorph PhysicalConfiguration PhysicalConfiguration)
    (physicalTranslate_zero_apply : ∀ A, physicalTranslate 0 A = A)
    (physicalTranslate_add_apply : ∀ s t A,
      physicalTranslate (s + t) A =
        physicalTranslate s (physicalTranslate t A))
    (latticeDisplacement : ∀ n, ℝ → PeriodicHypercubicVertex (sideLength n))
    (interpolate_equivariant : ∀ n t U,
      interpolate n
          (periodicHypercubicConfigurationTranslationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (sideLength n) (latticeDisplacement n t) U) =
        physicalTranslate t (interpolate n U)) :
    (periodicHypercubicSpecialUnitaryPhysicalEmbedding
      sideLength sideLength_pos N hN beta beta_nonneg
      interpolate interpolate_measurable
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).PhysicalTemporalAction where
  translate := physicalTranslate
  translate_zero_apply := physicalTranslate_zero_apply
  translate_add_apply := physicalTranslate_add_apply
  latticeTranslate n t :=
    periodicHypercubicConfigurationTranslationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (sideLength n) (latticeDisplacement n t)
  latticeTranslate_measurable n t :=
    (periodicHypercubicConfigurationTranslationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (sideLength n) (latticeDisplacement n t)).measurable
  latticeGibbs_map_eq_self n t := by
    letI : NeZero (sideLength n) :=
      ⟨Nat.ne_of_gt (sideLength_pos n)⟩
    change
      MeasureTheory.Measure.map
          (periodicHypercubicConfigurationTranslationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (sideLength n) (latticeDisplacement n t))
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (sideLength n) N hN (beta n) (beta_nonneg n)).gibbsMeasure =
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (sideLength n) N hN (beta n) (beta_nonneg n)).gibbsMeasure
    exact periodicHypercubicSpecialUnitary_gibbs_map_translation_eq_self
      (sideLength n) N hN (beta n) (beta_nonneg n)
      (latticeDisplacement n t)
  interpolate_equivariant := interpolate_equivariant

end

end MathlibAnalytic
end MGAP4D
