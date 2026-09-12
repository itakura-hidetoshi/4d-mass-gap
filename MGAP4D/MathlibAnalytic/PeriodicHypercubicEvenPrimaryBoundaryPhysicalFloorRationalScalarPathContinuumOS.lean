import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathCompactProkhorov
import Mathlib.Tactic

/-!
# One-sided primary scalar continuum rational-cylinder OS positivity

The preceding layers provide two independent ingredients on the same fixed
scalar carrier `ℚ → ℝ`:

* exact compact support of every finite Wilson-derived scalar path law, hence an
  actual Prokhorov subsequential weak limit; and
* finite scalar Osterwalder--Schrader positivity, together with a theorem that
  passes it to any weak limit once the explicit primary temporal reach diverges.

This file composes those ingredients along the very same Prokhorov subsequence.
The lattice spacing and primary temporal reach are reindexed by that subsequence;
strict monotonicity preserves both scaling limits.  No old full-boundary-vacuum
locality statement, cross-scale edge-carrier equality, physical-volume identity,
continuum reflection-positivity premise, or positive-time closedness premise is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Reindexing the spacing sequence and its selected lattice index by the same
subsequence leaves one finite scalar path law definitionally unchanged.  This
is the exact same-root bridge needed to feed the Prokhorov convergence theorem
into the subsequence-indexed scaling data. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_spacing_reindex
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (s : ℕ → ℕ)
    (n : ℕ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta latticeSpacing (s n) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        H N hN beta hbeta (fun k => latticeSpacing (s k)) n := by
  rfl

/-- The Prokhorov weak convergence can therefore be stated using the spacing
sequence already reindexed by its own subsequence. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.weakConvergence_reindexed
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          (fun k => latticeSpacing (L.subsequence k)) n)
      atTop
      (nhds L.continuumMeasure) := by
  simpa only [
    ← periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_spacing_reindex]
    using L.weakConvergence

/-- A strict Prokhorov subsequence preserves convergence of the lattice spacing
to zero. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.latticeSpacing_tendsto_zero
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (hzero : Tendsto latticeSpacing atTop (nhds 0)) :
    Tendsto
      (fun n => latticeSpacing (L.subsequence n))
      atTop
      (nhds 0) := by
  exact hzero.comp L.subsequence_strictMono.tendsto_atTop

/-- A strict Prokhorov subsequence also preserves divergence of the explicit
one-sided primary temporal reach. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.temporalReach_tendsto_atTop
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop) :
    Tendsto
      (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
        (fun n => H (L.subsequence n))
        (fun n => latticeSpacing (L.subsequence n)))
      atTop atTop := by
  have h := hreach.comp L.subsequence_strictMono.tendsto_atTop
  simpa [periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach] using h

/-- The actual Prokhorov continuum scalar path law satisfies the
Osterwalder--Schrader inequality for every bounded-continuous cylinder supported
at finitely many nonnegative rational times, provided only that the explicit
primary temporal reach diverges.

Finite positivity comes from the actual Wilson source; continuum nonnegativity
is produced by weak convergence and closedness, not assumed. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorov_continuum_reflectionForm_nonneg
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder) :
    0 ≤ Cyl.realReflectionForm (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  let H' : ℕ → ℕ := fun n => H (L.subsequence n)
  let beta' : ℕ → ℝ := fun n => beta (L.subsequence n)
  let latticeSpacing' : ℕ → ℝ := fun n => latticeSpacing (L.subsequence n)
  have hbeta' : ∀ n, 0 ≤ beta' n := by
    intro n
    exact hbeta (L.subsequence n)
  have hspacing' : ∀ n, 0 < latticeSpacing' n := by
    intro n
    exact latticeSpacing_pos (L.subsequence n)
  have hreach' :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H' latticeSpacing')
        atTop atTop := by
    simpa [H', latticeSpacing'] using
      L.temporalReach_tendsto_atTop H N hN beta hbeta latticeSpacing hreach
  have hweak' :
      Tendsto
        (fun n =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H' n) N hN (beta' n) (hbeta' n) latticeSpacing' n)
        atTop
        (nhds L.continuumMeasure) := by
    simpa [H', beta', latticeSpacing'] using
      L.weakConvergence_reindexed H N hN beta hbeta latticeSpacing
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_weakLimit_reflectionForm_nonneg_of_temporalReach
      H' N hN beta' hbeta' latticeSpacing' hspacing' hreach'
      L.continuumMeasure hweak' Cyl

/-- Existence package: compact trace range gives a same-root Prokhorov
continuum scalar path law, and along its selected subsequence both physical
scaling receipts are retained while every positive rational cylinder satisfies
OS reflection positivity.

The resulting object is the canonical primary-plaquette scalar process law; it
is not identified here with the full continuum gauge-field measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_continuumOS_exists
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop) :
    ∃ L :
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
          H N hN beta hbeta latticeSpacing,
      Tendsto
          (fun n => latticeSpacing (L.subsequence n))
          atTop (nhds 0) ∧
      Tendsto
          (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
            (fun n => H (L.subsequence n))
            (fun n => latticeSpacing (L.subsequence n)))
          atTop atTop ∧
      ∀ Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder,
        0 ≤ Cyl.realReflectionForm (L.continuumMeasure : Measure (ℚ → ℝ)) := by
  let L :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_prokhorovSubsequence_exists
      H N hN beta hbeta latticeSpacing).some
  refine ⟨L, ?_, ?_, ?_⟩
  · exact
      L.latticeSpacing_tendsto_zero
        H N hN beta hbeta latticeSpacing latticeSpacing_tendsto_zero
  · exact
      L.temporalReach_tendsto_atTop
        H N hN beta hbeta latticeSpacing hreach
  · intro Cyl
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorov_continuum_reflectionForm_nonneg
        H N hN beta hbeta latticeSpacing latticeSpacing_pos hreach L Cyl

end

end MathlibAnalytic
end MGAP4D
