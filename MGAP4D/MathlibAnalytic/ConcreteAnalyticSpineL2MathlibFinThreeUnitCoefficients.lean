import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitFamily

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A `Fin 3` coefficient function vanishes if its explicit three-term
coordinate-unit combination vanishes.

This is the first coefficient-kernel leaf for three coordinate units.  The proof
is coordinate-wise: evaluating at the three selected indices kills the two
off-diagonal terms and leaves the corresponding coefficient. -/
theorem concrete_l2_mathlib_fin_three_unit_coefficients_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hlin :
      r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0) :
    ∀ i : Fin 3, r i = 0 := by
  have hlin' :
      r 0 • concreteL2MathlibUnit a +
        r 1 • concreteL2MathlibUnit b +
          r 2 • concreteL2MathlibUnit c = 0 := by
    simpa [concreteL2MathlibFinThreeUnitFamily] using hlin
  have ha_fun := congrArg (fun x : lp (fun _ : ℕ => ℝ) 2 => x a) hlin'
  have ha : r 0 = 0 := by
    simpa [concrete_l2_mathlib_unit_apply_self,
      concrete_l2_mathlib_unit_apply_of_ne hab.symm,
      concrete_l2_mathlib_unit_apply_of_ne hac.symm,
      add_assoc] using ha_fun
  have hb_fun := congrArg (fun x : lp (fun _ : ℕ => ℝ) 2 => x b) hlin'
  have hb : r 1 = 0 := by
    simpa [concrete_l2_mathlib_unit_apply_self,
      concrete_l2_mathlib_unit_apply_of_ne hab,
      concrete_l2_mathlib_unit_apply_of_ne hbc.symm,
      add_assoc] using hb_fun
  have hc_fun := congrArg (fun x : lp (fun _ : ℕ => ℝ) 2 => x c) hlin'
  have hc : r 2 = 0 := by
    simpa [concrete_l2_mathlib_unit_apply_self,
      concrete_l2_mathlib_unit_apply_of_ne hac,
      concrete_l2_mathlib_unit_apply_of_ne hbc,
      add_assoc] using hc_fun
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- The first coefficient of a vanishing three-unit combination is zero. -/
theorem concrete_l2_mathlib_fin_three_unit_first_coeff_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hlin :
      r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0) :
    r 0 = 0 := by
  exact concrete_l2_mathlib_fin_three_unit_coefficients_zero hab hac hbc hlin 0

/-- The second coefficient of a vanishing three-unit combination is zero. -/
theorem concrete_l2_mathlib_fin_three_unit_second_coeff_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hlin :
      r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0) :
    r 1 = 0 := by
  exact concrete_l2_mathlib_fin_three_unit_coefficients_zero hab hac hbc hlin 1

/-- The third coefficient of a vanishing three-unit combination is zero. -/
theorem concrete_l2_mathlib_fin_three_unit_third_coeff_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hlin :
      r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0) :
    r 2 = 0 := by
  exact concrete_l2_mathlib_fin_three_unit_coefficients_zero hab hac hbc hlin 2

/-- Vanishing of the explicit `Fin 3` coordinate-unit combination is equivalent
to pointwise vanishing of the coefficient function. -/
theorem concrete_l2_mathlib_fin_three_unit_combination_eq_zero_iff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ} :
    r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0 ↔
      ∀ i : Fin 3, r i = 0 := by
  constructor
  · intro hlin
    exact concrete_l2_mathlib_fin_three_unit_coefficients_zero hab hac hbc hlin
  · intro hzero
    have h0 : r 0 = 0 := hzero 0
    have h1 : r 1 = 0 := hzero 1
    have h2 : r 2 = 0 := hzero 2
    simp [h0, h1, h2]

/-- Adapter predicate for the `Fin 3` coefficient-zero layer. -/
def concreteL2MathlibFinThreeUnitCoefficientsAdapter : Prop :=
  ∀ {a b c : ℕ}, a ≠ b → a ≠ c → b ≠ c → ∀ {r : Fin 3 → ℝ},
    (r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0 →
      ∀ i : Fin 3, r i = 0) ∧
    (r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 = 0 ↔
      ∀ i : Fin 3, r i = 0)

/-- Adapter theorem for the `Fin 3` coefficient-zero layer. -/
theorem concrete_l2_mathlib_fin_three_unit_coefficients_adapter_ready :
    concreteL2MathlibFinThreeUnitCoefficientsAdapter := by
  intro a b c hab hac hbc r
  exact ⟨
    by intro hlin; exact concrete_l2_mathlib_fin_three_unit_coefficients_zero hab hac hbc hlin,
    concrete_l2_mathlib_fin_three_unit_combination_eq_zero_iff hab hac hbc⟩

/-- Surface for the `Fin 3` coordinate-unit coefficient theorem in Mathlib
completed `ℓ²(ℕ, ℝ)`.

This layer proves that the explicit three-entry coefficient combination has only
the zero coefficient function in its kernel.  It remains below the finite-sum,
`LinearMap`, range, and general finite-family layers. -/
structure ConcreteL2MathlibFinThreeUnitCoefficientsSurface where
  finThreeFamilyReady : concreteAnalyticSpineL2MathlibFinThreeUnitFamilySurfaceReady
  coefficientsAdapter : concreteL2MathlibFinThreeUnitCoefficientsAdapter
  boundaryNotFinsetSumTheorem : Prop
  boundaryNotLinearMapTheorem : Prop
  boundaryNotRangeEquivTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete `Fin 3` coordinate-unit coefficient surface. -/
def concreteL2MathlibFinThreeUnitCoefficientsSurface :
    ConcreteL2MathlibFinThreeUnitCoefficientsSurface :=
  { finThreeFamilyReady := concrete_analytic_spine_l2_mathlib_fin_three_unit_family_surface_ready
    coefficientsAdapter := concrete_l2_mathlib_fin_three_unit_coefficients_adapter_ready
    boundaryNotFinsetSumTheorem := True
    boundaryNotLinearMapTheorem := True
    boundaryNotRangeEquivTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the `Fin 3` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitFamilySurfaceReady ∧
  concreteL2MathlibFinThreeUnitCoefficientsAdapter ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotFinsetSumTheorem ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotLinearMapTheorem ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotRangeEquivTheorem ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitCoefficientsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the `Fin 3` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_coefficients_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_family_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_coefficients_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial trivial

/-- Boundary marker for the `Fin 3` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsSurfaceReady

/-- Boundary theorem for the `Fin 3` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_coefficients_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_coefficients_surface_ready

end

end MathlibAnalytic
end MGAP4D
