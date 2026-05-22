import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnits

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Every vector in the two-unit synthesis range decomposes as the linear
combination of the two selected coordinate units with its reconstructed
coordinates.

This is the range-level reconstruction theorem in the ambient completed `ℓ²`
carrier. -/
theorem concrete_l2_mathlib_fin_two_unit_range_decomposition_val
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v • concreteL2MathlibUnit k +
        concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v • concreteL2MathlibUnit n := by
  have hsynth := concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize_val hkn v
  have hsum :
      ((concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
          (concreteL2MathlibFinTwoUnitRangeCoordinates hkn v)) :
          lp (fun _ : ℕ => ℝ) 2) =
        concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v • concreteL2MathlibUnit k +
          concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v • concreteL2MathlibUnit n := by
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [concrete_l2_mathlib_fin_two_unit_sum_eq_explicit]
    simp [concreteL2MathlibFinTwoUnitFamily,
      concreteL2MathlibFinTwoUnitRangeFirstCoordinate,
      concreteL2MathlibFinTwoUnitRangeSecondCoordinate]
  exact hsynth.symm.trans hsum

/-- Short alias for the first reconstructed coefficient in the two-unit range. -/
def concreteL2MathlibFinTwoUnitRangeDecompositionLeftCoeff
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) : ℝ :=
  concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v

/-- Short alias for the second reconstructed coefficient in the two-unit range. -/
def concreteL2MathlibFinTwoUnitRangeDecompositionRightCoeff
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) : ℝ :=
  concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v

/-- Decomposition using the short coefficient aliases. -/
theorem concrete_l2_mathlib_fin_two_unit_range_decomposition_val_alias
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinTwoUnitRangeDecompositionLeftCoeff hkn v • concreteL2MathlibUnit k +
        concreteL2MathlibFinTwoUnitRangeDecompositionRightCoeff hkn v • concreteL2MathlibUnit n := by
  unfold concreteL2MathlibFinTwoUnitRangeDecompositionLeftCoeff
  unfold concreteL2MathlibFinTwoUnitRangeDecompositionRightCoeff
  exact concrete_l2_mathlib_fin_two_unit_range_decomposition_val hkn v

/-- If a range vector is represented by a two-term coordinate-unit combination,
then the left scalar is its reconstructed first coordinate. -/
theorem concrete_l2_mathlib_fin_two_unit_range_decomposition_left_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {a b : ℝ}
    (hv : (v : lp (fun _ : ℕ => ℝ) 2) =
      a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n) :
    a = concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v := by
  let c : Fin 2 → ℝ := fun i => if i = 0 then a else b
  have hc : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v := by
    apply Subtype.ext
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [concrete_l2_mathlib_fin_two_unit_sum_eq_explicit]
    simpa [c, concreteL2MathlibFinTwoUnitFamily] using hv.symm
  have hcoords : c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v :=
    concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc
  have h0 := congrArg (fun f : Fin 2 → ℝ => f 0) hcoords
  simpa [c, concreteL2MathlibFinTwoUnitRangeFirstCoordinate] using h0

/-- If a range vector is represented by a two-term coordinate-unit combination,
then the right scalar is its reconstructed second coordinate. -/
theorem concrete_l2_mathlib_fin_two_unit_range_decomposition_right_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {a b : ℝ}
    (hv : (v : lp (fun _ : ℕ => ℝ) 2) =
      a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n) :
    b = concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v := by
  let c : Fin 2 → ℝ := fun i => if i = 0 then a else b
  have hc : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v := by
    apply Subtype.ext
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [concrete_l2_mathlib_fin_two_unit_sum_eq_explicit]
    simpa [c, concreteL2MathlibFinTwoUnitFamily] using hv.symm
  have hcoords : c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v :=
    concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc
  have h1 := congrArg (fun f : Fin 2 → ℝ => f 1) hcoords
  simpa [c, concreteL2MathlibFinTwoUnitRangeSecondCoordinate] using h1

/-- Adapter predicate for two-unit range decomposition and coefficient uniqueness. -/
def concreteL2MathlibFinTwoUnitRangeDecompositionAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      (v : lp (fun _ : ℕ => ℝ) 2) =
        concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v • concreteL2MathlibUnit k +
          concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v • concreteL2MathlibUnit n) ∧
    (∀ {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {a b : ℝ},
      (v : lp (fun _ : ℕ => ℝ) 2) = a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n →
        a = concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v ∧
        b = concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v)

/-- Adapter theorem for two-unit range decomposition and coefficient uniqueness. -/
theorem concrete_l2_mathlib_fin_two_unit_range_decomposition_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeDecompositionAdapter := by
  intro k n hkn
  exact ⟨
    by intro v; exact concrete_l2_mathlib_fin_two_unit_range_decomposition_val hkn v,
    by
      intro v a b hv
      exact ⟨
        concrete_l2_mathlib_fin_two_unit_range_decomposition_left_unique hkn hv,
        concrete_l2_mathlib_fin_two_unit_range_decomposition_right_unique hkn hv⟩⟩

/-- Surface for two-unit range decomposition in the ambient completed `ℓ²` carrier.

This layer proves that every vector in the two-unit synthesis range decomposes
uniquely as `a • e_k + b • e_n`, where `a` and `b` are the reconstructed range
coordinates.  It remains a two-coordinate range theorem and does not claim finite
dimensionality of the ambient space, a basis theorem, dense span,
finite-support-domain equivalence, or any operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeDecompositionSurface where
  rangeCoordinateUnitsReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsSurfaceReady
  rangeDecompositionAdapter : concreteL2MathlibFinTwoUnitRangeDecompositionAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete two-unit range decomposition surface. -/
def concreteL2MathlibFinTwoUnitRangeDecompositionSurface :
    ConcreteL2MathlibFinTwoUnitRangeDecompositionSurface :=
  { rangeCoordinateUnitsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_units_surface_ready
    rangeDecompositionAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_decomposition_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range decomposition surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionAdapter ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeDecompositionSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range decomposition surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_decomposition_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_units_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_decomposition_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range decomposition surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionSurfaceReady

/-- Boundary theorem for the two-unit range decomposition surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_decomposition_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_decomposition_surface_ready

end

end MathlibAnalytic
end MGAP4D
