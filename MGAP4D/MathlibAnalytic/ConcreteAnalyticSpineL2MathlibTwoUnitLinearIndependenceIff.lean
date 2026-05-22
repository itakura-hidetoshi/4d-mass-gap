import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibTwoUnitLinearIndependence

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The vanishing of a two-term linear combination of two distinct coordinate
units is equivalent to the vanishing of both scalar coefficients.

This packages the previous coefficient theorem into a reusable iff form. -/
theorem concrete_l2_mathlib_two_unit_linear_combination_eq_zero_iff
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ} :
    a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n = 0 ↔
      a = 0 ∧ b = 0 := by
  constructor
  · intro hlin
    exact concrete_l2_mathlib_two_unit_linear_independent_coefficients hkn hlin
  · intro hcoeff
    rcases hcoeff with ⟨ha, hb⟩
    subst ha
    subst hb
    simp

/-- If two scalar multiples of distinct coordinate units are equal, then both
scalars vanish.

This is the no-nontrivial-proportionality form of the two-unit linear
independence leaf. -/
theorem concrete_l2_mathlib_two_unit_smul_eq_smul_coefficients_zero
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ}
    (hEq : a • concreteL2MathlibUnit k = b • concreteL2MathlibUnit n) :
    a = 0 ∧ b = 0 := by
  have hlin : a • concreteL2MathlibUnit k + (-b) • concreteL2MathlibUnit n = 0 := by
    rw [hEq]
    simp
  have hcoeff :=
    concrete_l2_mathlib_two_unit_linear_independent_coefficients hkn hlin
  rcases hcoeff with ⟨ha, hneg_b⟩
  have hb : b = 0 := by
    exact neg_eq_zero.mp hneg_b
  exact ⟨ha, hb⟩

/-- If a scalar multiple of one coordinate unit equals another scalar multiple
of a distinct coordinate unit, the left scalar vanishes. -/
theorem concrete_l2_mathlib_two_unit_smul_eq_smul_left_coeff_zero
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ}
    (hEq : a • concreteL2MathlibUnit k = b • concreteL2MathlibUnit n) :
    a = 0 := by
  exact (concrete_l2_mathlib_two_unit_smul_eq_smul_coefficients_zero hkn hEq).1

/-- If a scalar multiple of one coordinate unit equals another scalar multiple
of a distinct coordinate unit, the right scalar vanishes. -/
theorem concrete_l2_mathlib_two_unit_smul_eq_smul_right_coeff_zero
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ}
    (hEq : a • concreteL2MathlibUnit k = b • concreteL2MathlibUnit n) :
    b = 0 := by
  exact (concrete_l2_mathlib_two_unit_smul_eq_smul_coefficients_zero hkn hEq).2

/-- Adapter predicate for the iff/no-proportionality two-unit layer. -/
def concreteL2MathlibTwoUnitLinearIndependenceIffAdapter : Prop :=
  (∀ {k n : ℕ}, k ≠ n → ∀ {a b : ℝ},
    (a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n = 0 ↔
      a = 0 ∧ b = 0)) ∧
  (∀ {k n : ℕ}, k ≠ n → ∀ {a b : ℝ},
    a • concreteL2MathlibUnit k = b • concreteL2MathlibUnit n →
      a = 0 ∧ b = 0)

/-- Iff/no-proportionality adapter theorem for two distinct coordinate units. -/
theorem concrete_l2_mathlib_two_unit_linear_independence_iff_adapter_ready :
    concreteL2MathlibTwoUnitLinearIndependenceIffAdapter := by
  exact ⟨
    by intro k n hkn a b; exact concrete_l2_mathlib_two_unit_linear_combination_eq_zero_iff hkn,
    by intro k n hkn a b hEq; exact concrete_l2_mathlib_two_unit_smul_eq_smul_coefficients_zero hkn hEq⟩

/-- Surface for the iff/no-proportionality form of two-coordinate-unit linear
independence in Mathlib completed `ℓ²(ℕ, ℝ)`.

This is a reuse layer: it does not prove a general finite-family theorem, but it
turns the two-coordinate coefficient theorem into an iff and a no-nontrivial
proportionality statement, ready for later finite-family and finite-support
handoffs. -/
structure ConcreteL2MathlibTwoUnitLinearIndependenceIffSurface where
  twoUnitLinearIndependenceReady : concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceSurfaceReady
  iffAdapter : concreteL2MathlibTwoUnitLinearIndependenceIffAdapter
  boundaryNotGeneralFiniteFamilyTheorem : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete Mathlib completed-`ℓ²` two-coordinate-unit iff surface. -/
def concreteL2MathlibTwoUnitLinearIndependenceIffSurface :
    ConcreteL2MathlibTwoUnitLinearIndependenceIffSurface :=
  { twoUnitLinearIndependenceReady :=
      concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_surface_ready
    iffAdapter := concrete_l2_mathlib_two_unit_linear_independence_iff_adapter_ready
    boundaryNotGeneralFiniteFamilyTheorem := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-coordinate-unit iff/no-proportionality surface. -/
def concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceIffSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceSurfaceReady ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffAdapter ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotGeneralFiniteFamilyTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibTwoUnitLinearIndependenceIffSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-coordinate-unit iff/no-proportionality surface. -/
theorem concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_iff_surface_ready :
    concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceIffSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceIffSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_surface_ready <|
      And.intro concrete_l2_mathlib_two_unit_linear_independence_iff_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the two-coordinate-unit iff/no-proportionality surface. -/
def concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceIffHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceIffSurfaceReady

/-- Boundary theorem for the two-coordinate-unit iff/no-proportionality surface. -/
theorem concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_iff_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceIffHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_iff_surface_ready

end

end MathlibAnalytic
end MGAP4D
