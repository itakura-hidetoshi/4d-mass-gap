import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialFiniteLawStationarity
import Mathlib.Tactic

/-!
# Factorial continuum finite-dimensional stationarity for the primary scalar path law

The preceding layer proves eventual exact equality, along the chosen Prokhorov subsequence at
canonical factorial spacing, between the shifted and unshifted finite-dimensional scalar laws on a
fixed nonnegative rational slot set `J`.

Both coordinate maps

`x ↦ (q ↦ x (q+t))` and `x ↦ (q ↦ x q)`

are continuous from the fixed scalar path carrier `ℚ → ℝ` to the fixed finite product `J → ℝ`.
Mathlib's continuous mapping theorem therefore sends the same scalar-path weak limit through each
map.  Eventual exact equality of the finite laws identifies the two mapped sequences, and uniqueness
of limits gives exact stationarity of the continuum finite-dimensional law.

No adjacent-step regularity premise, whole-path translation invariance, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- At canonical factorial spacing, every fixed finite collection of nonnegative rational scalar
coordinates has exactly the same continuum law after any fixed nonnegative rational time shift. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_finiteRestriction_law_stationary
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
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
          J t).measurable.aemeasurable =
      L.continuumMeasure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
          J).measurable.aemeasurable := by
  let μseq : ℕ → ProbabilityMeasure (ℚ → ℝ) := fun n =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence n)
  let τ : C(ℚ → ℝ, ∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
      J t
  let ρ : C(ℚ → ℝ, ∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap J
  have hweak : Tendsto μseq atTop (nhds L.continuumMeasure) := by
    simpa [μseq] using L.weakConvergence
  have hshift :
      Tendsto
        (fun n => (μseq n).map τ.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map τ.measurable.aemeasurable)) := by
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        μseq L.continuumMeasure hweak τ.continuous
  have hbase :
      Tendsto
        (fun n => (μseq n).map ρ.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map ρ.measurable.aemeasurable)) := by
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        μseq L.continuumMeasure hweak ρ.continuous
  have hfiniteMeasure :=
    L.factorial_finiteRestriction_law_eventually_stationary
      H N hN beta hbeta J hJ t ht
  have hfinite :
      (fun n => (μseq n).map τ.measurable.aemeasurable) =ᶠ[atTop]
        (fun n => (μseq n).map ρ.measurable.aemeasurable) := by
    filter_upwards [hfiniteMeasure] with n hn
    apply ProbabilityMeasure.toMeasure_injective
    change
      Measure.map τ
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)) =
        Measure.map ρ
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n))
    simpa [τ, ρ] using hn
  have hshift' :
      Tendsto
        (fun n => (μseq n).map ρ.measurable.aemeasurable)
        atTop
        (nhds (L.continuumMeasure.map τ.measurable.aemeasurable)) :=
    hshift.congr' hfinite
  exact tendsto_nhds_unique hshift' hbase

end

end MathlibAnalytic
end MGAP4D
