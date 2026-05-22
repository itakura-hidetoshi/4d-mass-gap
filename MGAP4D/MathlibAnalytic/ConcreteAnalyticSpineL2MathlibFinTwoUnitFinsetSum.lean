import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitCoefficients

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The `Fin 2` sum over the coordinate-unit family unfolds to the explicit
two-term combination.

This is the finite-sum handoff lemma from the concrete two-entry coefficient
surface to Mathlib's finite-family notation. -/
theorem concrete_l2_mathlib_fin_two_unit_sum_eq_explicit
    (k n : ℕ) (c : Fin 2 → ℝ) :
    (∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i) =
      c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 := by
  rw [Fin.sum_univ_two]

/-- If the finite sum of a `Fin 2` coordinate-unit combination vanishes, then
all coefficients vanish.

This is the `Finset.univ.sum` form of the previous explicit two-term coefficient
theorem. -/
theorem concrete_l2_mathlib_fin_two_unit_sum_coefficients_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hlin :
      (∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i) = 0) :
    ∀ i : Fin 2, c i = 0 := by
  rw [concrete_l2_mathlib_fin_two_unit_sum_eq_explicit] at hlin
  exact concrete_l2_mathlib_fin_two_unit_coefficients_zero hkn hlin

/-- The finite sum of a `Fin 2` coordinate-unit combination vanishes iff all
coefficients vanish. -/
theorem concrete_l2_mathlib_fin_two_unit_sum_eq_zero_iff
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ} :
    ((∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i) = 0) ↔
      ∀ i : Fin 2, c i = 0 := by
  constructor
  · intro hlin
    exact concrete_l2_mathlib_fin_two_unit_sum_coefficients_zero hkn hlin
  · intro hzero
    rw [concrete_l2_mathlib_fin_two_unit_sum_eq_explicit]
    have h0 : c 0 = 0 := hzero 0
    have h1 : c 1 = 0 := hzero 1
    simp [h0, h1]

/-- Adapter predicate for the finite-sum `Fin 2` coefficient-zero layer. -/
def concreteL2MathlibFinTwoUnitFinsetSumAdapter : Prop :=
  ∀ {k n : ℕ}, k ≠ n → ∀ {c : Fin 2 → ℝ},
    ((∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i) = 0 →
      ∀ i : Fin 2, c i = 0) ∧
    (((∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i) = 0) ↔
      ∀ i : Fin 2, c i = 0)

/-- Adapter theorem for the finite-sum `Fin 2` coefficient-zero layer. -/
theorem concrete_l2_mathlib_fin_two_unit_finset_sum_adapter_ready :
    concreteL2MathlibFinTwoUnitFinsetSumAdapter := by
  intro k n hkn c
  exact ⟨
    by intro hlin; exact concrete_l2_mathlib_fin_two_unit_sum_coefficients_zero hkn hlin,
    concrete_l2_mathlib_fin_two_unit_sum_eq_zero_iff hkn⟩

/-- Surface for the finite-sum `Fin 2` coordinate-unit coefficient theorem in
Mathlib completed `ℓ²(ℕ, ℝ)`.

This layer moves from the explicit two-term expression to Mathlib's finite-sum
notation over `Fin 2`.  It is the immediate handoff shape for later finite-family
linear-independence work, while preserving all hard residual boundaries. -/
structure ConcreteL2MathlibFinTwoUnitFinsetSumSurface where
  finTwoCoefficientsReady : concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsSurfaceReady
  finsetSumAdapter : concreteL2MathlibFinTwoUnitFinsetSumAdapter
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete finite-sum `Fin 2` coordinate-unit coefficient surface. -/
def concreteL2MathlibFinTwoUnitFinsetSumSurface :
    ConcreteL2MathlibFinTwoUnitFinsetSumSurface :=
  { finTwoCoefficientsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_coefficients_surface_ready
    finsetSumAdapter := concrete_l2_mathlib_fin_two_unit_finset_sum_adapter_ready
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the finite-sum `Fin 2` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitCoefficientsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitFinsetSumAdapter ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitFinsetSumSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the finite-sum `Fin 2` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_finset_sum_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_coefficients_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_finset_sum_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the finite-sum `Fin 2` coordinate-unit coefficient surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumSurfaceReady

/-- Boundary theorem for the finite-sum `Fin 2` coordinate-unit coefficient surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_finset_sum_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_finset_sum_surface_ready

end

end MathlibAnalytic
end MGAP4D
