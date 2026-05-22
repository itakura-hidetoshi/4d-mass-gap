import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUnique

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The two-unit synthesis map with codomain restricted to its range.

This is the canonical pre-equivalence map
`(Fin 2 → ℝ) →ₗ[ℝ] range(T)`.  It avoids choosing an inverse explicitly while
putting the previous injective `LinearMap` into the correct codomain for a later
`LinearEquiv` leaf. -/
def concreteL2MathlibFinTwoUnitSynthesisRangeMap (k n : ℕ) :
    (Fin 2 → ℝ) →ₗ[ℝ] concreteL2MathlibFinTwoUnitSynthesisRange k n where
  toFun c :=
    ⟨concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c,
      concrete_l2_mathlib_fin_two_unit_synthesis_mem_range k n c⟩
  map_add' := by
    intro c d
    ext
    exact map_add (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n) c d
  map_smul' := by
    intro a c
    ext
    exact map_smul (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n) a c

/-- The range-restricted synthesis map has the original synthesis vector as its
underlying value. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_map_apply_val
    (k n : ℕ) (c : Fin 2 → ℝ) :
    (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n c :
        lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c := by
  rfl

/-- The range-restricted synthesis map is injective when the two selected
indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_map_injective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) := by
  intro c d hmap
  apply concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_injective hkn
  exact congrArg (fun v : concreteL2MathlibFinTwoUnitSynthesisRange k n =>
    (v : lp (fun _ : ℕ => ℝ) 2)) hmap

/-- The range-restricted synthesis map is surjective onto the named range. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_map_surjective
    (k n : ℕ) :
    Function.Surjective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) := by
  intro v
  rcases v.property with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  ext
  exact hc

/-- The range-restricted synthesis map is bijective when the two selected indices
are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_map_bijective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) :=
  ⟨
    concrete_l2_mathlib_fin_two_unit_synthesis_range_map_injective hkn,
    concrete_l2_mathlib_fin_two_unit_synthesis_range_map_surjective k n⟩

/-- A range vector has a coefficient preimage for the range-restricted synthesis
map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_map_preimage_exists
    (k n : ℕ) (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    ∃ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitSynthesisRangeMap k n c = v :=
  concrete_l2_mathlib_fin_two_unit_synthesis_range_map_surjective k n v

/-- For distinct selected indices, the range-restricted coefficient preimage is
unique. -/
theorem concrete_l2_mathlib_fin_two_unit_range_map_preimage_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c d : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisRangeMap k n c = v)
    (hd : concreteL2MathlibFinTwoUnitSynthesisRangeMap k n d = v) :
    c = d := by
  exact concrete_l2_mathlib_fin_two_unit_synthesis_range_map_injective hkn
    (hc.trans hd.symm)

/-- Adapter predicate for the range-restricted two-unit synthesis map. -/
def concreteL2MathlibFinTwoUnitSynthesisRangeMapAdapter : Prop :=
  (∀ k n : ℕ, Function.Surjective
    (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n)) ∧
  (∀ {k n : ℕ}, k ≠ n → Function.Injective
    (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n)) ∧
  (∀ {k n : ℕ}, k ≠ n → Function.Bijective
    (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n))

/-- Adapter theorem for the range-restricted two-unit synthesis map. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_map_adapter_ready :
    concreteL2MathlibFinTwoUnitSynthesisRangeMapAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_synthesis_range_map_surjective k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_synthesis_range_map_injective hkn,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_synthesis_range_map_bijective hkn⟩

/-- Surface for the range-restricted `Fin 2` coordinate-unit synthesis map.

This is the immediate pre-`LinearEquiv` layer: the synthesis map is now a
`LinearMap` into its own range, and for distinct indices it is bijective.  The
leaf deliberately stops short of constructing the explicit `LinearEquiv`, and
keeps all later basis, dimension, dense-span, and operator-theoretic claims as
separate boundaries. -/
structure ConcreteL2MathlibFinTwoUnitSynthesisRangeMapSurface where
  preimageUniqueReady : concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueSurfaceReady
  rangeMapAdapter : concreteL2MathlibFinTwoUnitSynthesisRangeMapAdapter
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

/-- Concrete range-restricted two-unit synthesis map surface. -/
def concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface :
    ConcreteL2MathlibFinTwoUnitSynthesisRangeMapSurface :=
  { preimageUniqueReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_preimage_unique_surface_ready
    rangeMapAdapter := concrete_l2_mathlib_fin_two_unit_synthesis_range_map_adapter_ready
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

/-- Readiness for the range-restricted two-unit synthesis map surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueSurfaceReady ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapAdapter ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotRangeLinearEquivTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeMapSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the range-restricted two-unit synthesis map surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_map_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_preimage_unique_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_synthesis_range_map_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the range-restricted two-unit synthesis map surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapSurfaceReady

/-- Boundary theorem for the range-restricted two-unit synthesis map surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_map_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_map_surface_ready

end

end MathlibAnalytic
end MGAP4D
