import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRange

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The three-unit synthesis map with codomain restricted to its range.

This is the canonical pre-equivalence map
`(Fin 3 → ℝ) →ₗ[ℝ] range(T)`. -/
def concreteL2MathlibFinThreeUnitSynthesisRangeMap (a b c : ℕ) :
    (Fin 3 → ℝ) →ₗ[ℝ] concreteL2MathlibFinThreeUnitSynthesisRange a b c where
  toFun r :=
    ⟨concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r,
      concrete_l2_mathlib_fin_three_unit_synthesis_mem_range a b c r⟩
  map_add' := by
    intro r s
    exact Subtype.ext
      (map_add (concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c) r s)
  map_smul' := by
    intro t r
    exact Subtype.ext
      (map_smul (concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c) t r)

/-- The range-restricted synthesis map has the original synthesis vector as its
underlying value. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_map_apply_val
    (a b c : ℕ) (r : Fin 3 → ℝ) :
    (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c r :
        lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r := by
  rfl

/-- The range-restricted three-unit synthesis map is injective under pairwise
distinct index assumptions. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_map_injective
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c) := by
  intro r s hrs
  apply concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_injective hab hac hbc
  exact congrArg (fun v : concreteL2MathlibFinThreeUnitSynthesisRange a b c =>
    (v : lp (fun _ : ℕ => ℝ) 2)) hrs

/-- The range-restricted three-unit synthesis map is surjective onto the named
range. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_map_surjective
    (a b c : ℕ) :
    Function.Surjective (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c) := by
  intro v
  rcases v.property with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  exact Subtype.ext hr

/-- The range-restricted three-unit synthesis map is bijective when the selected
indices are pairwise distinct. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_map_bijective
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Bijective (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c) :=
  ⟨
    concrete_l2_mathlib_fin_three_unit_synthesis_range_map_injective hab hac hbc,
    concrete_l2_mathlib_fin_three_unit_synthesis_range_map_surjective a b c⟩

/-- A range vector has a coefficient preimage for the range-restricted synthesis
map. -/
theorem concrete_l2_mathlib_fin_three_unit_range_map_preimage_exists
    (a b c : ℕ) (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) :
    ∃ r : Fin 3 → ℝ,
      concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c r = v :=
  concrete_l2_mathlib_fin_three_unit_synthesis_range_map_surjective a b c v

/-- For pairwise distinct selected indices, the range-restricted coefficient
preimage is unique. -/
theorem concrete_l2_mathlib_fin_three_unit_range_map_preimage_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r s : Fin 3 → ℝ}
    (hr : concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c r = v)
    (hs : concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c s = v) :
    r = s := by
  exact concrete_l2_mathlib_fin_three_unit_synthesis_range_map_injective hab hac hbc
    (hr.trans hs.symm)

/-- Adapter predicate for the range-restricted three-unit synthesis map. -/
def concreteL2MathlibFinThreeUnitSynthesisRangeMapAdapter : Prop :=
  (∀ a b c : ℕ, Function.Surjective
    (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c)) ∧
  (∀ {a b c : ℕ}, a ≠ b → a ≠ c → b ≠ c → Function.Injective
    (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c)) ∧
  (∀ {a b c : ℕ}, a ≠ b → a ≠ c → b ≠ c → Function.Bijective
    (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c))

/-- Adapter theorem for the range-restricted three-unit synthesis map. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_map_adapter_ready :
    concreteL2MathlibFinThreeUnitSynthesisRangeMapAdapter := by
  exact ⟨
    by intro a b c; exact concrete_l2_mathlib_fin_three_unit_synthesis_range_map_surjective a b c,
    by intro a b c hab hac hbc; exact concrete_l2_mathlib_fin_three_unit_synthesis_range_map_injective hab hac hbc,
    by intro a b c hab hac hbc; exact concrete_l2_mathlib_fin_three_unit_synthesis_range_map_bijective hab hac hbc⟩

/-- Surface for the range-restricted `Fin 3` coordinate-unit synthesis map. -/
structure ConcreteL2MathlibFinThreeUnitSynthesisRangeMapSurface where
  rangeReady : concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeSurfaceReady
  rangeMapAdapter : concreteL2MathlibFinThreeUnitSynthesisRangeMapAdapter
  boundaryNotRangeLinearEquivTheorem : Prop
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete range-restricted three-unit synthesis map surface. -/
def concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface :
    ConcreteL2MathlibFinThreeUnitSynthesisRangeMapSurface :=
  { rangeReady := concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_surface_ready
    rangeMapAdapter := concrete_l2_mathlib_fin_three_unit_synthesis_range_map_adapter_ready
    boundaryNotRangeLinearEquivTheorem := True
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the range-restricted three-unit synthesis map surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeSurfaceReady ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapAdapter ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotRangeLinearEquivTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeMapSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the range-restricted three-unit synthesis map surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_map_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_synthesis_range_map_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the range-restricted three-unit synthesis map surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapSurfaceReady

/-- Boundary theorem for the range-restricted three-unit synthesis map surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_map_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_map_surface_ready

end

end MathlibAnalytic
end MGAP4D
