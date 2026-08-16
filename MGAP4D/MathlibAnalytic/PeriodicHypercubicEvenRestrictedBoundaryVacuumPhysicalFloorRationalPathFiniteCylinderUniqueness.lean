import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftAction
import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Equality of all finite rational-coordinate marginals determines equality of
full rational-path measures.

This is the countable-product uniqueness step needed after finite-cylinder
stationarity has been proved.  It does not manufacture joint stationarity from
one-coordinate marginals: the finite-cylinder hypothesis is explicit. -/
theorem rationalPathMeasure_eq_of_finite_restrict_eq
    (μ ν : Measure (ℚ → ℝ))
    (hfinite : ∀ J : Finset ℚ,
      Measure.map J.restrict μ = Measure.map J.restrict ν) :
    μ = ν := by
  let P : ∀ J : Finset ℚ, Measure (∀ q : J, ℝ) :=
    fun J => Measure.map J.restrict ν
  have hμ : IsProjectiveLimit (α := fun _ : ℚ => ℝ) μ P := by
    intro J
    exact hfinite J
  have hν : IsProjectiveLimit (α := fun _ : ℚ => ℝ) ν P := by
    intro J
    rfl
  exact hμ.unique hν

/-- Full rational path-law stationarity follows once every finite rational
cylinder has the same law before and after the fixed rational translation.

The proof is pure projective-limit uniqueness on the countable Polish product
`ℝ^ℚ`; all physical work is therefore isolated in the finite-cylinder premise. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_shift_eq_of_finite_cylinder_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Filter.Tendsto latticeSpacing Filter.atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Filter.Tendsto physicalVolume Filter.atTop Filter.atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (r : ℚ)
    (hfinite : ∀ J : Finset ℚ,
      Measure.map J.restrict
          (ProbabilityMeasure.toMeasure
            (L.continuumMeasure.map
              (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable)) =
        Measure.map J.restrict
          (ProbabilityMeasure.toMeasure L.continuumMeasure)) :
    L.continuumMeasure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable =
      L.continuumMeasure := by
  apply ProbabilityMeasure.toMeasure_injective
  exact rationalPathMeasure_eq_of_finite_restrict_eq
    (ProbabilityMeasure.toMeasure
      (L.continuumMeasure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable))
    (ProbabilityMeasure.toMeasure L.continuumMeasure)
    hfinite

end

end MathlibAnalytic
end MGAP4D
