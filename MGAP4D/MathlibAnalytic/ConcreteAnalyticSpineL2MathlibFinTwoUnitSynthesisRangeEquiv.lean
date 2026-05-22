import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range-restricted two-unit synthesis map as a `LinearEquiv` onto its range.

The inverse is chosen by classical choice from the previously proved
surjectivity.  The left inverse follows from injectivity, and the right inverse
is exactly the chosen preimage property.  This remains a two-entry range
equivalence leaf, not a general finite-family basis or dimension theorem. -/
def concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv
    {k n : ℕ} (hkn : k ≠ n) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] concreteL2MathlibFinTwoUnitSynthesisRange k n :=
  LinearEquiv.ofBijective
    (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n)
    (concrete_l2_mathlib_fin_two_unit_synthesis_range_map_bijective hkn)

/-- The forward map of the range `LinearEquiv` is the range-restricted synthesis
map. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply
    {k n : ℕ} (hkn : k ≠ n) (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c =
      concreteL2MathlibFinTwoUnitSynthesisRangeMap k n c := by
  rfl

/-- The underlying value of the range `LinearEquiv` is the original synthesis
linear map. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val
    {k n : ℕ} (hkn : k ≠ n) (c : Fin 2 → ℝ) :
    (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c :
        lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c := by
  rfl

/-- The range `LinearEquiv` is injective. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_injective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) := by
  exact (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).injective

/-- The range `LinearEquiv` is surjective. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surjective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Surjective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) := by
  exact (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).surjective

/-- Every vector in the two-unit synthesis range has a coefficient vector given
by the inverse of the range `LinearEquiv`. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_inverse_witness
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        ((concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).symm v) = v := by
  exact (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).apply_symm_apply v

/-- The inverse coefficient vector is unique: any coefficient vector synthesizing
to the same range vector equals the inverse image under the range `LinearEquiv`. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_inverse_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v) :
    c = (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).symm v := by
  exact Eq.symm ((concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).symm_apply_eq.mpr hc)

/-- Adapter predicate for the two-unit synthesis range `LinearEquiv` layer. -/
def concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) ∧
    Function.Surjective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn)

/-- Adapter theorem for the two-unit synthesis range `LinearEquiv` layer. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_adapter_ready :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivAdapter := by
  intro k n hkn
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_injective hkn,
    concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surjective hkn⟩

/-- Surface for the two-unit synthesis range `LinearEquiv`.

This layer completes the finite two-coordinate carrier equivalence between the
coefficient space `Fin 2 → ℝ` and the range of the synthesis map.  It deliberately
stops at the range equivalence and does not claim finite dimensionality of any
larger space, a basis theorem, dense span, finite-support-domain equivalence, or
operator-theoretic closure. -/
structure ConcreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface where
  rangeMapReady : concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapSurfaceReady
  rangeLinearEquivAdapter : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete range `LinearEquiv` surface for the two-unit synthesis map. -/
def concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface :
    ConcreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface :=
  { rangeMapReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_map_surface_ready
    rangeLinearEquivAdapter :=
      concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit synthesis range `LinearEquiv` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeMapSurfaceReady ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivAdapter ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit synthesis range `LinearEquiv` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_map_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit synthesis range `LinearEquiv` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurfaceReady

/-- Boundary theorem for the two-unit synthesis range `LinearEquiv` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surface_ready

end

end MathlibAnalytic
end MGAP4D
