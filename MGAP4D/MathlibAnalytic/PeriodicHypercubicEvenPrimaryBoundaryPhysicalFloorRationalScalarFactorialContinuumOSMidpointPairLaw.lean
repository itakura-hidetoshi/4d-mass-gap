import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSMidpointPairLaw
import Mathlib.Tactic

/-!
# Factorial continuum OS midpoint pair law on the primary scalar path

The preceding finite layer proves eventual exact equality, along the canonical factorial primary
scalar Prokhorov subsequence, between the translated OS symmetric pair law

`(x (-(q+t)), x (q+t))`

and the midpoint pair law

`(x (-q), x ((q+t)+t))`

on the fixed carrier `(J → ℝ) × (J → ℝ)`.

Both pair maps are continuous.  Mathlib's continuous mapping theorem therefore sends the same
scalar-path weak limit through each map.  Eventual exact equality identifies the two mapped finite
sequences, and uniqueness of limits yields the exact continuum pair-law identity.

No OS contraction, null-space preservation, semigroup, Hamiltonian, spectral statement, or
mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- At canonical factorial spacing, the continuum law of the translated OS symmetric scalar pair is
exactly the law of the corresponding midpoint pair for every fixed finite nonnegative rational slot
set and every nonnegative rational shift. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_osShiftedPair_law_eq_midpoint
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t) :
    L.continuumMeasure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
          J t).measurable.aemeasurable =
      L.continuumMeasure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
          J t).measurable.aemeasurable := by
  let μseq : ℕ → ProbabilityMeasure (ℚ → ℝ) := fun n =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence n)
  let P : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap
      J t
  let Q : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap
      J t
  have hweak : Tendsto μseq atTop (nhds L.continuumMeasure) := by
    simpa [μseq] using L.weakConvergence
  have hshift :
      Tendsto
        (fun n => (μseq n).map P.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map P.measurable.aemeasurable)) := by
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        μseq L.continuumMeasure hweak P.continuous
  have hmidpoint :
      Tendsto
        (fun n => (μseq n).map Q.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map Q.measurable.aemeasurable)) := by
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        μseq L.continuumMeasure hweak Q.continuous
  have hfiniteMeasure :=
    L.factorial_osShiftedPair_law_eventually_eq_midpoint
      H N hN beta hbeta J hJ t ht
  have hfinite :
      (fun n => (μseq n).map P.measurable.aemeasurable) =ᶠ[atTop]
        (fun n => (μseq n).map Q.measurable.aemeasurable) := by
    filter_upwards [hfiniteMeasure] with n hn
    apply ProbabilityMeasure.toMeasure_injective
    change
      Measure.map P
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) =
        Measure.map Q
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n))
    simpa [P, Q] using hn
  have hshift' :
      Tendsto
        (fun n => (μseq n).map Q.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map P.measurable.aemeasurable)) :=
    hshift.congr' hfinite
  exact tendsto_nhds_unique hshift' hmidpoint

end

end MathlibAnalytic
end MGAP4D
