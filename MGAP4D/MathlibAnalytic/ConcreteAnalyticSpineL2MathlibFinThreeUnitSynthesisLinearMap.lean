import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernel

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The `Fin 3` coordinate-unit synthesis as a genuine `LinearMap`.

This is the three-entry analogue of the merged `Fin 2` synthesis `LinearMap`
leaf.  It promotes the named finite synthesis function to Mathlib's linear-map
API without claiming any general finite-family theorem, basis theorem, dense span,
or operator statement. -/
def concreteL2MathlibFinThreeUnitSynthesisLinearMap (a b c : ℕ) :
    (Fin 3 → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun := concreteL2MathlibFinThreeUnitSynthesis a b c
  map_add' := by
    intro r s
    unfold concreteL2MathlibFinThreeUnitSynthesis
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro t r
    unfold concreteL2MathlibFinThreeUnitSynthesis
    simp [Pi.smul_apply, smul_smul]

/-- The linear map agrees definitionally with the named synthesis function. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply
    (a b c : ℕ) (r : Fin 3 → ℝ) :
    concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r =
      concreteL2MathlibFinThreeUnitSynthesis a b c r := by
  rfl

/-- The linear-map synthesis unfolds to the finite sum. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply_eq_sum
    (a b c : ℕ) (r : Fin 3 → ℝ) :
    concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r =
      ∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i := by
  rfl

/-- The linear-map synthesis has trivial zero fiber. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_eq_zero_iff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ} :
    concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r = 0 ↔
      ∀ i : Fin 3, r i = 0 := by
  change concreteL2MathlibFinThreeUnitSynthesis a b c r = 0 ↔ ∀ i : Fin 3, r i = 0
  exact concrete_l2_mathlib_fin_three_unit_synthesis_eq_zero_iff hab hac hbc

/-- If the linear-map synthesis vanishes, then all coefficients vanish. -/
theorem concrete_l2_mathlib_fin_three_unit_coefficients_zero_of_linear_map_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hzero : concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r = 0) :
    ∀ i : Fin 3, r i = 0 := by
  exact (concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_eq_zero_iff hab hac hbc).mp hzero

/-- If all coefficients vanish, then the linear-map synthesis vanishes. -/
theorem concrete_l2_mathlib_fin_three_unit_linear_map_zero_of_coefficients_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hcoeff : ∀ i : Fin 3, r i = 0) :
    concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r = 0 := by
  exact (concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_eq_zero_iff hab hac hbc).mpr hcoeff

/-- The kernel of the three-unit synthesis linear map is the bottom submodule. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_ker_eq_bot
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearMap.ker (concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c) = ⊥ := by
  ext r
  constructor
  · intro hr
    have hzero : concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r = 0 := hr
    have hcoeff : ∀ i : Fin 3, r i = 0 :=
      concrete_l2_mathlib_fin_three_unit_coefficients_zero_of_linear_map_zero hab hac hbc hzero
    ext i
    exact hcoeff i
  · intro hr
    have hcoeff : ∀ i : Fin 3, r i = 0 := by
      intro i
      exact congrArg (fun f : Fin 3 → ℝ => f i) hr
    exact concrete_l2_mathlib_fin_three_unit_linear_map_zero_of_coefficients_zero hab hac hbc hcoeff

/-- The three-unit synthesis linear map is injective. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_injective
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c) := by
  rw [← LinearMap.ker_eq_bot]
  exact concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_ker_eq_bot hab hac hbc

/-- Adapter predicate for the three-unit synthesis `LinearMap` layer. -/
def concreteL2MathlibFinThreeUnitSynthesisLinearMapAdapter : Prop :=
  ∀ {a b c : ℕ}, a ≠ b → a ≠ c → b ≠ c →
    LinearMap.ker (concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c) = ⊥ ∧
    Function.Injective (concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c)

/-- Adapter theorem for the three-unit synthesis `LinearMap` layer. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_adapter_ready :
    concreteL2MathlibFinThreeUnitSynthesisLinearMapAdapter := by
  intro a b c hab hac hbc
  exact ⟨
    concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_ker_eq_bot hab hac hbc,
    concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_injective hab hac hbc⟩

/-- Surface for the `Fin 3` coordinate-unit synthesis `LinearMap` in Mathlib
completed `ℓ²(ℕ, ℝ)`.

This layer promotes the named three-unit synthesis operation to a Mathlib
`LinearMap` and proves that its kernel is trivial and hence the map is injective.
It remains strictly three-entry and does not claim general finite-family linear
independence, range equivalence, or basis theorem. -/
structure ConcreteL2MathlibFinThreeUnitSynthesisLinearMapSurface where
  synthesisKernelReady : concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelSurfaceReady
  linearMapAdapter : concreteL2MathlibFinThreeUnitSynthesisLinearMapAdapter
  boundaryNotRangeEquivTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete three-unit synthesis `LinearMap` surface. -/
def concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface :
    ConcreteL2MathlibFinThreeUnitSynthesisLinearMapSurface :=
  { synthesisKernelReady := concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_kernel_surface_ready
    linearMapAdapter := concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_adapter_ready
    boundaryNotRangeEquivTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the three-unit synthesis `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisLinearMapSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelSurfaceReady ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapAdapter ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotRangeEquivTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitSynthesisLinearMapSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the three-unit synthesis `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_linear_map_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisLinearMapSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisLinearMapSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_kernel_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the three-unit synthesis `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisLinearMapHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisLinearMapSurfaceReady

/-- Boundary theorem for the three-unit synthesis `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_linear_map_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisLinearMapHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_linear_map_surface_ready

end

end MathlibAnalytic
end MGAP4D
