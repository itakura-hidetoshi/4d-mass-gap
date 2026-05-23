import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range-restricted three-unit synthesis map as a `LinearEquiv` onto its range.

This is the three-entry analogue of the merged `Fin 2` range-equivalence leaf. -/
def concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] concreteL2MathlibFinThreeUnitSynthesisRange a b c :=
  LinearEquiv.ofBijective
    (concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c)
    (concrete_l2_mathlib_fin_three_unit_synthesis_range_map_bijective hab hac hbc)

/-- The forward map of the range `LinearEquiv` is the range-restricted synthesis
map. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (r : Fin 3 → ℝ) :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r =
      concreteL2MathlibFinThreeUnitSynthesisRangeMap a b c r := by
  rfl

/-- The underlying value of the range `LinearEquiv` is the original synthesis
linear map. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply_val
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (r : Fin 3 → ℝ) :
    (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r :
        lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinThreeUnitSynthesisLinearMap a b c r := by
  rfl

/-- The range `LinearEquiv` is injective. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_injective
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc) := by
  exact (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).injective

/-- The range `LinearEquiv` is surjective. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_surjective
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Surjective (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc) := by
  exact (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).surjective

/-- Every vector in the three-unit synthesis range has a coefficient vector given
by the inverse of the range `LinearEquiv`. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_inverse_witness
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        ((concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).symm v) = v := by
  exact (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).apply_symm_apply v

/-- The inverse coefficient vector is unique: any coefficient vector synthesizing
to the same range vector equals the inverse image under the range `LinearEquiv`. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_inverse_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ}
    (hr : concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v) :
    r = (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).symm v := by
  exact Eq.symm ((concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).symm_apply_eq.mpr hr.symm)

/-- Adapter predicate for the three-unit synthesis range `LinearEquiv` layer. -/
def concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivAdapter : Prop :=
  ∀ {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c),
    Function.Injective (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc) ∧
    Function.Surjective (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc)

/-- Adapter theorem for the three-unit synthesis range `LinearEquiv` layer. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_adapter_ready :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivAdapter := by
  intro a b c hab hac hbc
  exact ⟨
    concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_injective hab hac hbc,
    concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_surjective hab hac hbc⟩

/-- Surface for the three-unit synthesis range `LinearEquiv`.

This layer completes the finite three-coordinate carrier equivalence between the
coefficient space `Fin 3 → ℝ` and the range of the synthesis map.  It deliberately
stops at the range equivalence and does not claim finite dimensionality of any
larger space, a basis theorem, dense span, finite-support-domain equivalence, or
operator-theoretic closure. -/
structure ConcreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface where
  rangeMapReady : concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapSurfaceReady
  rangeLinearEquivAdapter : concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete range `LinearEquiv` surface for the three-unit synthesis map. -/
def concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface :
    ConcreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface :=
  { rangeMapReady :=
      concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_map_surface_ready
    rangeLinearEquivAdapter :=
      concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the three-unit synthesis range `LinearEquiv` surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeMapSurfaceReady ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivAdapter ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the three-unit synthesis range `LinearEquiv` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_map_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the three-unit synthesis range `LinearEquiv` surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurfaceReady

/-- Boundary theorem for the three-unit synthesis range `LinearEquiv` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_surface_ready

end

end MathlibAnalytic
end MGAP4D
