import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOS
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenGibbsReflection
import Mathlib.Tactic

/-!
# Reflection invariance of the one-sided primary scalar continuum path law

The reflection-completed primary readout was constructed so that physical
configuration reflection is exactly intrinsic rational-path reflection.  The
actual finite Wilson Gibbs law is independently known to be reflection
invariant.  Therefore the completed path law, and hence its canonical plaquette
scalarization on the fixed carrier `ℚ → ℝ`, are reflection invariant at every
finite scale.

This file proves that exact finite statement and then passes it through the same
Prokhorov weak limit used for continuum scalar OS positivity.  Continuity of
`x(q) ↦ x(-q)` and Mathlib's continuous mapping theorem for probability
measures give reflection invariance of the continuum scalar law.

No positivity premise, old full-boundary-vacuum locality statement, cross-scale
edge identification, physical-volume identity, or continuum symmetry premise
is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

local instance primaryScalarReflectionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryScalarReflectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryScalarReflectionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryScalarReflectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryScalarReflectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Intrinsic reflection on the fixed scalar rational path carrier is
continuous in the product topology. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_continuous :
    Continuous
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection := by
  apply continuous_pi
  intro q
  exact continuous_apply (-q)

/-- Scalarization of the reflection-completed primary readout is exactly
covariant under physical finite-configuration reflection. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectionCompletedReadout_configurationReflection
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n
          (periodicHypercubicEvenConfigurationReflection H A)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A)) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection]
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_reflection
      H N
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A)

/-- Audit-visible direct-source identity: the scalar finite path law is the
pushforward of the same actual Wilson Gibbs measure by the composed completed
primary readout and canonical plaquette scalarization. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_eq_map_wilsonSource
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            H latticeSpacing n))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
  exact
    Measure.map_map
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
        H N)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
        H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n)

/-- Every actual finite scalar path law is exactly invariant under intrinsic
rational-time reflection. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_reflection_map_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measure.map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n := by
  let X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      H latticeSpacing n
  let S :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
  let O :
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) →
        (ℚ → ℝ) :=
    S ∘ X
  have hX : Measurable X := by
    dsimp [X]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
        H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n
  have hS : Measurable S := by
    dsimp [S]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable
        H N
  have hO : Measurable O := by
    exact hS.comp hX
  have hcov :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection ∘ O =
        O ∘ periodicHypercubicEvenConfigurationReflection H := by
    funext A
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectionCompletedReadout_configurationReflection
        H N latticeSpacing n A).symm
  have hdirect :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_eq_map_wilsonSource
      H N hN beta hbeta latticeSpacing n
  rw [hdirect]
  calc
    Measure.map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (Measure.map O
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection ∘ O)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      Measure.map_map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable
        hO
    _ = Measure.map
        (O ∘ periodicHypercubicEvenConfigurationReflection H)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      rw [hcov]
    _ = Measure.map O
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_observable_law_invariant
        H N hN beta hbeta O hO

/-- Probability-measure version of exact finite scalar reflection invariance. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_reflection_map_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n).map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable.aemeasurable =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing n := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_reflection_map_eq_self
      H N hN beta hbeta latticeSpacing n

/-- Reflection invariance passes through the same Prokhorov weak limit.  This is
an application of Mathlib's continuous mapping theorem and uniqueness of weak
limits; no continuum reflection-invariance premise is used. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.continuumMeasure_reflection_map_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing) :
    L.continuumMeasure.map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_continuous.measurable.aemeasurable =
      L.continuumMeasure := by
  let μseq : ℕ → ProbabilityMeasure (ℚ → ℝ) := fun n =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      latticeSpacing (L.subsequence n)
  have hmap :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      μseq L.continuumMeasure (by simpa [μseq] using L.weakConvergence)
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_continuous
  have hfinite :
      ∀ n,
        (μseq n).map
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_continuous.measurable.aemeasurable =
          μseq n := by
    intro n
    dsimp [μseq]
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_reflection_map_eq_self
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        latticeSpacing (L.subsequence n)
  have hmap' :
      Tendsto μseq atTop
        (nhds
          (L.continuumMeasure.map
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_continuous.measurable.aemeasurable)) := by
    simpa only [hfinite] using hmap
  have hbase : Tendsto μseq atTop (nhds L.continuumMeasure) := by
    simpa [μseq] using L.weakConvergence
  exact tendsto_nhds_unique hmap' hbase

/-- Existence of a same-root scalar continuum law carrying both positive
rational-cylinder OS positivity and exact intrinsic reflection invariance. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_continuumOS_reflectionInvariant_exists
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop) :
    ∃ L :
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
          H N hN beta hbeta latticeSpacing,
      Tendsto (fun n => latticeSpacing (L.subsequence n)) atTop (nhds 0) ∧
      Tendsto
          (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
            (fun n => H (L.subsequence n))
            (fun n => latticeSpacing (L.subsequence n)))
          atTop atTop ∧
      (∀ Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder,
        0 ≤ Cyl.realReflectionForm (L.continuumMeasure : Measure (ℚ → ℝ))) ∧
      L.continuumMeasure.map
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_continuous.measurable.aemeasurable =
        L.continuumMeasure := by
  obtain ⟨L, hzero, hreachL, hOS⟩ :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_continuumOS_exists
      H N hN beta hbeta latticeSpacing latticeSpacing_pos
      latticeSpacing_tendsto_zero hreach
  refine ⟨L, hzero, hreachL, hOS, ?_⟩
  exact
    L.continuumMeasure_reflection_map_eq_self H N hN beta hbeta latticeSpacing

end

end MathlibAnalytic
end MGAP4D
