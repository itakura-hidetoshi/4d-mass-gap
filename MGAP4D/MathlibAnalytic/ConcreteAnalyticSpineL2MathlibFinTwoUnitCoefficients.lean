import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitFamily

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- A `Fin 2` coefficient function vanishes if its two-term coordinate-unit
combination vanishes.

This is the finite-family-shaped restatement of the two-coordinate-unit linear
independence theorem.  It is intentionally still a two-entry coefficient theorem,
not a general finite-family `LinearIndependent` theorem. -/
theorem concrete_l2_mathlib_fin_two_unit_coefficients_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hlin :
      c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 = 0) :
    ∀ i : Fin 2, c i = 0 := by
  have hlin' :
      c 0 • concreteL2MathlibUnit k + c 1 • concreteL2MathlibUnit n = 0 := by
    simpa [concreteL2MathlibFinTwoUnitFamily] using hlin
  have hcoeff :=
    concrete_l2_mathlib_two_unit_linear_independent_coefficients hkn hlin'
  intro i
  fin_cases i
  · exact hcoeff.1
  · exact hcoeff.2

/-- The first coefficient of a vanishing `Fin 2` coordinate-unit combination is
zero. -/
theorem concrete_l2_mathlib_fin_two_unit_left_coeff_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hlin :
      c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 = 0) :
    c 0 = 0 := by
  exact concrete_l2_mathlib_fin_two_unit_coefficients_zero hkn hlin 0

/-- The second coefficient of a vanishing `Fin 2` coordinate-unit combination is
zero. -/
theorem concrete_l2_mathlib_fin_two_unit_right_coeff_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hlin :
      c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 = 0) :
    c 1 = 0 := by
  exact concrete_l2_mathlib_fin_two_unit_coefficients_zero hkn hlin 1

/-- Vanishing of the explicit `Fin 2` coordinate-unit combination is equivalent
to pointwise vanishing of the coefficient function. -/
theorem concrete_l2_mathlib_fin_two_unit_combination_eq_zero_iff
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ} :
    c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 = 0 ↔
      ∀ i : Fin 2, c i = 0 := by
  constructor
  · intro hlin
    exact concrete_l2_mathlib_fin_two_unit_coefficients_zero hkn hlin
  · intro hzero
    have h0 : c 0 = 0 := hzero 0
    have h1 : c 1 = 0 := hzero 1
    simp [h0, h1]

/-- Adapter predicate for the `Fin 2` coefficient-zero layer. -/
def concreteL2MathlibFinTwoUnitCoefficientsAdapter : Prop :=
  ∀ {k n : ℕ}, k ≠ n → ∀ {c : Fin 2 → ℝ},
    (c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 = 0 →
      ∀ i : Fin 2, c i = 0) ∧
    (c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 = 0 ↔
      ∀ i : Fin 2, c i = 0)

/-- Adapter theorem for the `Fin 2` coefficient-zero layer. -/
theorem concrete_l2_mathlib_fin_two_unit_coefficients_adapter_ready :
    concreteL2MathlibFinTwoUnitCoefficientsAdapter := by
  intro k n hkn c
  exact ⟨
    by intro hlin; exact concrete_l2_mathlib_fin_two_unit_coefficients_zero hkn hlin,
    concrete_l2_mathlib_fin_two_unit_combination_eq_zero_iff hkn⟩

/-- Surface for the `Fin 2` coordinate-unit coefficient theorem in Mathlib
completed `ℓ²(ℕ, ℝ)`.

This is the first coefficient-function shaped layer: the explicit two-entry
linear combination indexed by `Fin 2` has only the zero coefficient function in
its kernel.  It remains below a general finite-family `LinearIndependent` theorem
and preserves all downstream hard boundaries. -/
structure ConcreteL2MathlibFinTwoUnitCoefficientsSurface where
  finTwoFamilyReady : concreteAnalyticSpineL2MathlibFinTwoUnitFamilySurfaceReady
  coefficientsAdapter : concreteL2MathlibFinTwoUnitCoefficientsAdapter
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete `Fin 2` coordinate-unit coefficient surface. -/
def concreteL2MathlibFinTwoUnitCoefficientsSurface :
    ConcreteL2MathlibFinTwoUnitCoefficientsSurface :=
  { finTwoFamilyReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_family_surface_ready
    coefficientsAdapter := concrete_l2_mathlib_fin_two_unit_coefficients_adapter_ready
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the `Fin 2` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitFamilySurfaceReady ∧
  concreteL2MathlibFinTwoUnitCoefficientsAdapter ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitCoefficientsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the `Fin 2` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_coefficients_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_family_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_coefficients_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the `Fin 2` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsSurfaceReady

/-- Boundary theorem for the `Fin 2` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_coefficients_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_coefficients_surface_ready

end

end MathlibAnalytic
end MGAP4D
