import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitCoefficients

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The `Fin 3` sum over the coordinate-unit family unfolds to the explicit
three-term combination.

This is the finite-sum handoff lemma from the concrete three-entry coefficient
surface to Mathlib's finite-family notation. -/
theorem concrete_l2_mathlib_fin_three_unit_sum_eq_explicit
    (a b c : ℕ) (r : Fin 3 → ℝ) :
    (∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i) =
      r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 := by
  rw [Fin.sum_univ_three]

/-- If the finite sum of a `Fin 3` coordinate-unit combination vanishes, then
all coefficients vanish. -/
theorem concrete_l2_mathlib_fin_three_unit_sum_coefficients_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hlin :
      (∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i) = 0) :
    ∀ i : Fin 3, r i = 0 := by
  rw [concrete_l2_mathlib_fin_three_unit_sum_eq_explicit] at hlin
  exact concrete_l2_mathlib_fin_three_unit_coefficients_zero hab hac hbc hlin

/-- The finite sum of a `Fin 3` coordinate-unit combination vanishes iff all
coefficients vanish. -/
theorem concrete_l2_mathlib_fin_three_unit_sum_eq_zero_iff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ} :
    ((∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i) = 0) ↔
      ∀ i : Fin 3, r i = 0 := by
  constructor
  · intro hlin
    exact concrete_l2_mathlib_fin_three_unit_sum_coefficients_zero hab hac hbc hlin
  · intro hzero
    rw [concrete_l2_mathlib_fin_three_unit_sum_eq_explicit]
    have h0 : r 0 = 0 := hzero 0
    have h1 : r 1 = 0 := hzero 1
    have h2 : r 2 = 0 := hzero 2
    simp [h0, h1, h2]

/-- Adapter predicate for the finite-sum `Fin 3` coefficient-zero layer. -/
def concreteL2MathlibFinThreeUnitFinsetSumAdapter : Prop :=
  ∀ {a b c : ℕ}, a ≠ b → a ≠ c → b ≠ c → ∀ {r : Fin 3 → ℝ},
    ((∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i) = 0 →
      ∀ i : Fin 3, r i = 0) ∧
    (((∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i) = 0) ↔
      ∀ i : Fin 3, r i = 0)

/-- Adapter theorem for the finite-sum `Fin 3` coefficient-zero layer. -/
theorem concrete_l2_mathlib_fin_three_unit_finset_sum_adapter_ready :
    concreteL2MathlibFinThreeUnitFinsetSumAdapter := by
  intro a b c hab hac hbc r
  exact ⟨
    by intro hlin; exact concrete_l2_mathlib_fin_three_unit_sum_coefficients_zero hab hac hbc hlin,
    concrete_l2_mathlib_fin_three_unit_sum_eq_zero_iff hab hac hbc⟩

/-- Surface for the finite-sum `Fin 3` coordinate-unit coefficient theorem in
Mathlib completed `ℓ²(ℕ, ℝ)`.

This layer moves from the explicit three-term expression to Mathlib's finite-sum
notation over `Fin 3`.  It is the immediate handoff shape toward a named
synthesis map and later `LinearMap` layer, while preserving hard boundaries. -/
structure ConcreteL2MathlibFinThreeUnitFinsetSumSurface where
  finThreeCoefficientsReady : concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsSurfaceReady
  finsetSumAdapter : concreteL2MathlibFinThreeUnitFinsetSumAdapter
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

/-- Concrete finite-sum `Fin 3` coordinate-unit coefficient surface. -/
def concreteL2MathlibFinThreeUnitFinsetSumSurface :
    ConcreteL2MathlibFinThreeUnitFinsetSumSurface :=
  { finThreeCoefficientsReady :=
      concrete_analytic_spine_l2_mathlib_fin_three_unit_coefficients_surface_ready
    finsetSumAdapter := concrete_l2_mathlib_fin_three_unit_finset_sum_adapter_ready
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

/-- Readiness for the finite-sum `Fin 3` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitCoefficientsSurfaceReady ∧
  concreteL2MathlibFinThreeUnitFinsetSumAdapter ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotLinearMapTheorem ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotRangeEquivTheorem ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitFinsetSumSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the finite-sum `Fin 3` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_finset_sum_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_coefficients_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_finset_sum_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the finite-sum `Fin 3` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumSurfaceReady

/-- Boundary theorem for the finite-sum `Fin 3` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_finset_sum_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_finset_sum_surface_ready

end

end MathlibAnalytic
end MGAP4D
