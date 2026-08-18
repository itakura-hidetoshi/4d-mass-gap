import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalPathIntrinsicWilsonOS
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarMeasureReflection
import Mathlib.Tactic

/-!
# Reflection-completed primary rational path law and intrinsic finite OS positivity

The preceding finite Wilson-source theorem writes the Osterwalder--Schrader
quadratic integrand intrinsically as `F(X A) * F(Θ (X A))`, but still integrates
over the underlying finite Wilson configuration.

This file proves measurability of the reflection-completed primary rational path
`X`, pushes the same actual finite Wilson Gibbs law forward along `X`, and then
uses `integral_map` to transport the already-proved nonnegative quadratic form
to the finite rational path law itself.

The path carrier remains finite-scale and depends on `H`.  No cross-scale raw
edge identification, continuum premise, reflection-positivity premise,
half-extent growth premise, physical-volume identity, `sorry`, `admit`, or
`axiom` is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Intrinsic rational path reflection is measurable: it is just reindexing by
`q ↦ -q` in the countable product measurable space. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
        (Gauge := Gauge) H) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_pi_apply (-q)

/-- The reflection-completed primary rational path readout is measurable.

The nonnegative branch is the existing measurable raw path readout.  The
negative branch is the same readout after physical configuration reflection;
measurability of that reflection is reused from the existing finite product-Haar
measure-preserving theorem. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
    (H : ℕ)
    (Gauge : Type)
    [Group Gauge]
    [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge]
    [CompactSpace Gauge]
    [MeasurableSpace Gauge]
    [BorelSpace Gauge]
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Gauge) H latticeSpacing n) := by
  have hreflection :
      Measurable
        (periodicHypercubicEvenConfigurationReflection
          (Gauge := Gauge) H) :=
    (periodicHypercubicEvenConfigurationReflection_measurePreserving H Gauge).measurable
  have hraw :
      Measurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout
          (Gauge := Gauge) H latticeSpacing n) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_measurable
      (Gauge := Gauge) H latticeSpacing n
  apply measurable_pi_lambda
  intro q
  by_cases hq : 0 ≤ q
  · simp only [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
      if_pos hq]
    exact (measurable_pi_apply q).comp hraw
  · simp only [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout,
      if_neg hq]
    exact (measurable_pi_apply (-q)).comp (hraw.comp hreflection)

local instance primaryCompletedPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryCompletedPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryCompletedPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryCompletedPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryCompletedPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual finite reflection-completed primary rational path law, obtained by
direct pushforward of the same Wilson Gibbs measure used in the finite RP
proof. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measure
      (ℚ →
        (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  Measure.map
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      H latticeSpacing n)
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure

/-- Probability-measure packaging of the same reflection-completed finite path
law. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    ProbabilityMeasure
      (ℚ →
        (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsProbabilityMeasure.map
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
        H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n).aemeasurable

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n :
        Measure
          (ℚ →
            (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  rfl

/-- Audit-visible same-root identity: the completed path law is exactly the
pushforward of the actual finite Wilson Gibbs measure along the completed
readout. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure_eq_map_wilson
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
        H N hN beta hbeta latticeSpacing n =
      Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  rfl

/-- Actual finite reflection positivity on the completed rational path law.

For every bounded measurable cylinder supported on finitely many admissible
nonnegative rational slots,

`∫ F(x) F(Θx) dμ_path(x) ≥ 0`.

This is obtained only by pushing forward the intrinsic Wilson-source theorem;
no reflection-positivity assumption is added. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure_intrinsicReflectionPositive_boundedMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n J)
    (g :
      (∀ q : J,
        PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u, ‖g u‖ ≤ M) :
    0 ≤ ∫ x,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          H J g x *
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          H J g
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H x)
      ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  have hX :
      Measurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          H latticeSpacing n) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
      H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n
  have hF :
      Measurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H J g) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_measurable
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H J g hg
  have hTheta :
      Measurable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection_measurable
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H
  have hIntegrand :
      Measurable
        (fun x =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
              H J g x *
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder
              H J g
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection H x)) :=
    hF.mul (hF.comp hTheta)
  have hsource :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathCylinder_wilsonSource_intrinsicReflectionPositive_boundedMeasurable
      H N hN beta hbeta latticeSpacing n J hslots g hg M hM hbound
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
  rw [MeasureTheory.integral_map hX.aemeasurable hIntegrand.aestronglyMeasurable]
  exact hsource

end

end MathlibAnalytic
end MGAP4D
