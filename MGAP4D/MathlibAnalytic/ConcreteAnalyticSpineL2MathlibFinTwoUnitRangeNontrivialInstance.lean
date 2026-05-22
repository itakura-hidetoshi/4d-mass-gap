import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A direct `Nontrivial` instance for the two-unit synthesis range when the
selected indices are distinct.

This is intentionally packaged as a theorem rather than a global instance, so it
cannot unexpectedly affect typeclass search downstream. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial
    {k n : ℕ} (hkn : k ≠ n) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  refine ⟨⟨
    concreteL2MathlibFinTwoUnitFirstRangeVector k n,
    concreteL2MathlibFinTwoUnitSecondRangeVector k n,
    ?_⟩⟩
  exact concrete_l2_mathlib_fin_two_unit_range_vectors_ne hkn

/-- A direct `Nontrivial` instance from positive distance of the two distinguished
range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_of_dist_pos
    {k n : ℕ}
    (hpos : 0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n)) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  exact concrete_l2_mathlib_fin_two_unit_range_nontrivial
    ((concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos_iff).mp hpos)

/-- The distinguished range-vector inequality gives a `Nontrivial` witness. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_of_vectors_ne
    {k n : ℕ}
    (hne : concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n) :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  refine ⟨⟨
    concreteL2MathlibFinTwoUnitFirstRangeVector k n,
    concreteL2MathlibFinTwoUnitSecondRangeVector k n,
    hne⟩⟩

/-- The two-unit range is nontrivial iff the selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_iff
    {k n : ℕ} :
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) ↔ k ≠ n := by
  constructor
  · intro hnon hkn
    have hsub : Subsingleton (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
      subst hkn
      infer_instance
    exact not_subsingleton_iff_nontrivial.mpr hnon hsub
  · intro hkn
    exact concrete_l2_mathlib_fin_two_unit_range_nontrivial hkn

/-- The two-unit range is subsingleton iff the selected indices are equal. -/
theorem concrete_l2_mathlib_fin_two_unit_range_subsingleton_iff
    {k n : ℕ} :
    Subsingleton (concreteL2MathlibFinTwoUnitSynthesisRange k n) ↔ k = n := by
  constructor
  · intro hsub
    by_contra hkn
    exact concrete_l2_mathlib_fin_two_unit_range_not_subsingleton hkn hsub
  · intro hkn
    subst hkn
    infer_instance

/-- Adapter predicate for the local `Nontrivial` surface of the two-unit synthesis
range. -/
def concreteL2MathlibFinTwoUnitRangeNontrivialInstanceAdapter : Prop :=
  (∀ {k n : ℕ}, k ≠ n →
    Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n)) ∧
  (∀ {k n : ℕ},
    (Nontrivial (concreteL2MathlibFinTwoUnitSynthesisRange k n) ↔ k ≠ n)) ∧
  (∀ {k n : ℕ},
    (Subsingleton (concreteL2MathlibFinTwoUnitSynthesisRange k n) ↔ k = n))

/-- Adapter theorem for the local `Nontrivial` surface of the two-unit synthesis
range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_instance_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeNontrivialInstanceAdapter := by
  exact ⟨
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_nontrivial hkn,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_nontrivial_iff,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_subsingleton_iff⟩

/-- Surface for local nontriviality of the two-unit synthesis range.

The theorem supplies `Nontrivial range(T)` from `k ≠ n` without installing a global
instance.  This keeps typeclass effects local while preserving the geometric
meaning of the two distinguished range vectors. -/
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
