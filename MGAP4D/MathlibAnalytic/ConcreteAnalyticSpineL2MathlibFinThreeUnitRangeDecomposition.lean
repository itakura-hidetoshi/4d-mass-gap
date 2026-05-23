import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinates

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Reconstruct a range vector from its three recovered coefficients as an
explicit linear combination of the three selected coordinate units. -/
theorem concrete_l2_mathlib_fin_three_unit_range_decompose_val
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinThreeUnitRangeFirstCoordinate hab hac hbc v • concreteL2MathlibUnit a +
        concreteL2MathlibFinThreeUnitRangeSecondCoordinate hab hac hbc v • concreteL2MathlibUnit b +
          concreteL2MathlibFinThreeUnitRangeThirdCoordinate hab hac hbc v • concreteL2MathlibUnit c := by
  have hsynth :=
    concrete_l2_mathlib_fin_three_unit_range_coordinates_synthesize_val hab hac hbc v
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply_val] at hsynth
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply_eq_sum] at hsynth
  rw [Fin.sum_univ_three] at hsynth
  simpa [concreteL2MathlibFinThreeUnitRangeCoordinates,
    concreteL2MathlibFinThreeUnitRangeFirstCoordinate,
    concreteL2MathlibFinThreeUnitRangeSecondCoordinate,
    concreteL2MathlibFinThreeUnitRangeThirdCoordinate,
    concreteL2MathlibFinThreeUnitFamily] using hsynth.symm

/-- Range-subtype form of the three-unit coordinate decomposition. -/
theorem concrete_l2_mathlib_fin_three_unit_range_decompose_subtype
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) :
    v =
      concreteL2MathlibFinThreeUnitRangeFirstCoordinate hab hac hbc v •
          concreteL2MathlibFinThreeUnitFirstRangeVector a b c +
        concreteL2MathlibFinThreeUnitRangeSecondCoordinate hab hac hbc v •
          concreteL2MathlibFinThreeUnitSecondRangeVector a b c +
          concreteL2MathlibFinThreeUnitRangeThirdCoordinate hab hac hbc v •
            concreteL2MathlibFinThreeUnitThirdRangeVector a b c := by
  apply Subtype.ext
  simpa [concreteL2MathlibFinThreeUnitFirstRangeVector,
    concreteL2MathlibFinThreeUnitSecondRangeVector,
    concreteL2MathlibFinThreeUnitThirdRangeVector] using
    concrete_l2_mathlib_fin_three_unit_range_decompose_val hab hac hbc v

/-- The coordinate decomposition is unique at the coefficient level. -/
theorem concrete_l2_mathlib_fin_three_unit_range_decompose_coefficients_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ}
    (hr :
      (v : lp (fun _ : ℕ => ℝ) 2) =
        r 0 • concreteL2MathlibUnit a +
          r 1 • concreteL2MathlibUnit b +
            r 2 • concreteL2MathlibUnit c) :
    r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v := by
  have hsynth :
      concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v := by
    apply Subtype.ext
    rw [concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply_val]
    rw [concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply_eq_sum]
    rw [Fin.sum_univ_three]
    simpa [concreteL2MathlibFinThreeUnitFamily] using hr.symm
  exact concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc hsynth

/-- Adapter predicate for the three-unit range-decomposition layer. -/
def concreteL2MathlibFinThreeUnitRangeDecompositionAdapter : Prop :=
  ∀ {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c),
    (∀ v : concreteL2MathlibFinThreeUnitSynthesisRange a b c,
      (v : lp (fun _ : ℕ => ℝ) 2) =
        concreteL2MathlibFinThreeUnitRangeFirstCoordinate hab hac hbc v • concreteL2MathlibUnit a +
          concreteL2MathlibFinThreeUnitRangeSecondCoordinate hab hac hbc v • concreteL2MathlibUnit b +
            concreteL2MathlibFinThreeUnitRangeThirdCoordinate hab hac hbc v • concreteL2MathlibUnit c) ∧
    (∀ v : concreteL2MathlibFinThreeUnitSynthesisRange a b c,
      v =
        concreteL2MathlibFinThreeUnitRangeFirstCoordinate hab hac hbc v •
            concreteL2MathlibFinThreeUnitFirstRangeVector a b c +
          concreteL2MathlibFinThreeUnitRangeSecondCoordinate hab hac hbc v •
            concreteL2MathlibFinThreeUnitSecondRangeVector a b c +
            concreteL2MathlibFinThreeUnitRangeThirdCoordinate hab hac hbc v •
              concreteL2MathlibFinThreeUnitThirdRangeVector a b c)

/-- Adapter theorem for the three-unit range-decomposition layer. -/
theorem concrete_l2_mathlib_fin_three_unit_range_decomposition_adapter_ready :
    concreteL2MathlibFinThreeUnitRangeDecompositionAdapter := by
  intro a b c hab hac hbc
  exact ⟨
    by intro v; exact concrete_l2_mathlib_fin_three_unit_range_decompose_val hab hac hbc v,
    by intro v; exact concrete_l2_mathlib_fin_three_unit_range_decompose_subtype hab hac hbc v⟩

/-- Surface for explicit decomposition of vectors in the three-unit synthesis range.

This layer states that every vector in `range(T)` is exactly the linear
combination of the three selected coordinate units with its recovered coordinate
coefficients. -/
structure ConcreteL2MathlibFinThreeUnitRangeDecompositionSurface where
  rangeUnitCoordinatesReady : concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesSurfaceReady
  rangeDecompositionAdapter : concreteL2MathlibFinThreeUnitRangeDecompositionAdapter
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete three-unit range-decomposition surface. -/
def concreteL2MathlibFinThreeUnitRangeDecompositionSurface :
    ConcreteL2MathlibFinThreeUnitRangeDecompositionSurface :=
  { rangeUnitCoordinatesReady := concrete_analytic_spine_l2_mathlib_fin_three_unit_range_unit_coordinates_surface_ready
    rangeDecompositionAdapter := concrete_l2_mathlib_fin_three_unit_range_decomposition_adapter_ready
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the three-unit range-decomposition surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitRangeDecompositionSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesSurfaceReady ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionAdapter ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitRangeDecompositionSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the three-unit range-decomposition surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_range_decomposition_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitRangeDecompositionSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitRangeDecompositionSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_range_unit_coordinates_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_range_decomposition_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the three-unit range-decomposition surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitRangeDecompositionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitRangeDecompositionSurfaceReady

/-- Boundary theorem for the three-unit range-decomposition surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_range_decomposition_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitRangeDecompositionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_range_decomposition_surface_ready

end

end MathlibAnalytic
end MGAP4D
