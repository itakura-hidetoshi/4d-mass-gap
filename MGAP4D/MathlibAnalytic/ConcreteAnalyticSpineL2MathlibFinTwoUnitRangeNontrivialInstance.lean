import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A local `Nontrivial` theorem for the two-unit synthesis range.

Even when the two selected indices coincide, the range contains the nonzero
coordinate unit.  This is intentionally packaged as a theorem rather than a
global instance, so it cannot unexpectedly affect typeclass search downstream. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial
    (k n : ℕ) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  refine ⟨⟨0, concreteL2MathlibFinTwoUnitFirstRangeVector k n, ?_⟩⟩
  intro hzero
  exact concrete_l2_mathlib_fin_two_unit_first_range_vector_ne_zero k n hzero.symm

/-- A direct `Nontrivial` theorem from positive distance of the two distinguished
range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_of_dist_pos
    {k n : ℕ}
    (_hpos : 0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n)) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  exact concrete_l2_mathlib_fin_two_unit_range_nontrivial k n

/-- The distinguished range-vector inequality gives a `Nontrivial` witness. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_of_vectors_ne
    {k n : ℕ}
    (_hne : concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  exact concrete_l2_mathlib_fin_two_unit_range_nontrivial k n

/-- The two-unit range is always nontrivial. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_all
    (k n : ℕ) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) :=
  concrete_l2_mathlib_fin_two_unit_range_nontrivial k n

/-- If the selected indices are distinct, the range is not subsingleton. -/
theorem concrete_l2_mathlib_fin_two_unit_range_not_subsingleton_of_ne
    {k n : ℕ} (hkn : k ≠ n) :
    ¬ Subsingleton (concreteL2MathlibFinTwoUnitSynthesisRange k n) :=
  concrete_l2_mathlib_fin_two_unit_range_not_subsingleton hkn

/-- Adapter predicate for the local `Nontrivial` surface of the two-unit synthesis
range. -/
def concreteL2MathlibFinTwoUnitRangeNontrivialInstanceAdapter : Prop :=
  (∀ k n : ℕ,
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n)) ∧
  (∀ {k n : ℕ}, k ≠ n →
    ¬ Subsingleton (concreteL2MathlibFinTwoUnitSynthesisRange k n)) ∧
  (∀ {k n : ℕ}, k ≠ n →
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n))

/-- Adapter theorem for the local `Nontrivial` surface of the two-unit synthesis
range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_instance_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeNontrivialInstanceAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_nontrivial k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_not_subsingleton_of_ne hkn,
    by intro k n _hkn; exact concrete_l2_mathlib_fin_two_unit_range_nontrivial k n⟩

/-- Surface for local nontriviality of the two-unit synthesis range.

The theorem supplies `Nontrivial range(T)` for all `k,n` without installing a
global instance.  For `k ≠ n`, it also preserves the stronger not-subsingleton
witness from the two distinguished range vectors. -/
structure ConcreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface where
  rangeGeometryReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometrySurfaceReady
  rangeNontrivialInstanceAdapter : concreteL2MathlibFinTwoUnitRangeNontrivialInstanceAdapter
  boundaryNoGlobalInstanceInstalled : Prop
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete local nontriviality surface for the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface :
    ConcreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface :=
  { rangeGeometryReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_geometry_surface_ready
    rangeNontrivialInstanceAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_nontrivial_instance_adapter_ready
    boundaryNoGlobalInstanceInstalled := True
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the local nontriviality surface of the two-unit synthesis range. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometrySurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceAdapter ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNoGlobalInstanceInstalled ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialInstanceSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the local nontriviality surface of the two-unit synthesis
range. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_instance_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_geometry_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_nontrivial_instance_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the local nontriviality surface of the two-unit synthesis
range. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceSurfaceReady

/-- Boundary theorem for the local nontriviality surface of the two-unit synthesis
range. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_instance_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_instance_surface_ready

end

end MathlibAnalytic
end MGAP4D
