import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernel

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The `Fin 2` coordinate-unit synthesis as a genuine `LinearMap`.

This is still a two-entry, carrier-level leaf.  It promotes the previously named
finite synthesis function to Mathlib's linear-map API without claiming any
general finite-family theorem, basis theorem, dense-span theorem, or operator
statement. -/
def concreteL2MathlibFinTwoUnitSynthesisLinearMap (k n : ℕ) :
    (Fin 2 → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun := concreteL2MathlibFinTwoUnitSynthesis k n
  map_add' := by
    intro c d
    unfold concreteL2MathlibFinTwoUnitSynthesis
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    unfold concreteL2MathlibFinTwoUnitSynthesis
    simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

/-- The linear map agrees definitionally with the named synthesis function. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply
    (k n : ℕ) (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
      concreteL2MathlibFinTwoUnitSynthesis k n c := by
  rfl

/-- The linear-map synthesis unfolds to the finite sum. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum
    (k n : ℕ) (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
      ∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i := by
  rfl

/-- The linear-map synthesis has trivial zero fiber. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_eq_zero_iff
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ} :
    concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = 0 ↔
      ∀ i : Fin 2, c i = 0 := by
  change concreteL2MathlibFinTwoUnitSynthesis k n c = 0 ↔ ∀ i : Fin 2, c i = 0
  exact concrete_l2_mathlib_fin_two_unit_synthesis_eq_zero_iff hkn

/-- If the linear-map synthesis vanishes, then all coefficients vanish. -/
theorem concrete_l2_mathlib_fin_two_unit_coefficients_zero_of_linear_map_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hzero : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = 0) :
    ∀ i : Fin 2, c i = 0 := by
  exact (concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_eq_zero_iff hkn).mp hzero

/-- If all coefficients vanish, then the linear-map synthesis vanishes. -/
theorem concrete_l2_mathlib_fin_two_unit_linear_map_zero_of_coefficients_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hcoeff : ∀ i : Fin 2, c i = 0) :
    concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = 0 := by
  exact (concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_eq_zero_iff hkn).mpr hcoeff

/-- The kernel of the two-unit synthesis linear map is the bottom submodule. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_ker_eq_bot
    {k n : ℕ} (hkn : k ≠ n) :
    LinearMap.ker (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n) = ⊥ := by
  ext c
  constructor
  · intro hc
    have hzero : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = 0 := hc
    have hcoeff : ∀ i : Fin 2, c i = 0 :=
      concrete_l2_mathlib_fin_two_unit_coefficients_zero_of_linear_map_zero hkn hzero
    ext i
    exact hcoeff i
  · intro hc
    have hcoeff : ∀ i : Fin 2, c i = 0 := by
      intro i
      exact congrArg (fun f : Fin 2 → ℝ => f i) hc
    exact concrete_l2_mathlib_fin_two_unit_linear_map_zero_of_coefficients_zero hkn hcoeff

/-- The two-unit synthesis linear map is injective. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_injective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n) := by
  rw [← LinearMap.ker_eq_bot]
  exact concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_ker_eq_bot hkn

/-- Adapter predicate for the two-unit synthesis `LinearMap` layer. -/
def concreteL2MathlibFinTwoUnitSynthesisLinearMapAdapter : Prop :=
  ∀ {k n : ℕ}, k ≠ n →
    LinearMap.ker (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n) = ⊥ ∧
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n)

/-- Adapter theorem for the two-unit synthesis `LinearMap` layer. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_adapter_ready :
    concreteL2MathlibFinTwoUnitSynthesisLinearMapAdapter := by
  intro k n hkn
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_ker_eq_bot hkn,
    concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_injective hkn⟩

/-- Surface for the `Fin 2` coordinate-unit synthesis `LinearMap` in Mathlib
completed `ℓ²(ℕ, ℝ)`.

This layer promotes the named finite synthesis operation to a Mathlib `LinearMap`
and proves that its kernel is trivial and hence the map is injective.  It remains
strictly two-entry and does not claim a general finite-family linear-independence
or basis theorem. -/
structure ConcreteL2MathlibFinTwoUnitSynthesisLinearMapSurface where
  synthesisKernelReady : concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelSurfaceReady
  linearMapAdapter : concreteL2MathlibFinTwoUnitSynthesisLinearMapAdapter
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete two-unit synthesis `LinearMap` surface. -/
def concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface :
    ConcreteL2MathlibFinTwoUnitSynthesisLinearMapSurface :=
  { synthesisKernelReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_kernel_surface_ready
    linearMapAdapter :=
      concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_adapter_ready
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit synthesis `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisLinearMapSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelSurfaceReady ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapAdapter ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitSynthesisLinearMapSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit synthesis `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_linear_map_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisLinearMapSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisLinearMapSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_kernel_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the two-unit synthesis `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisLinearMapHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisLinearMapSurfaceReady

/-- Boundary theorem for the two-unit synthesis `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_linear_map_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisLinearMapHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_linear_map_surface_ready

end

end MathlibAnalytic
end MGAP4D
