import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitFinsetSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The finite synthesis map associated to the two selected coordinate units.

This is deliberately introduced first as a named function rather than as a
`LinearMap`: the present leaf captures the kernel-trivial theorem already proved
for the `Finset.univ.sum` expression, while keeping the later linear-map API
handoff as a separate boundary. -/
def concreteL2MathlibFinTwoUnitSynthesis (k n : ℕ) (c : Fin 2 → ℝ) :
    lp (fun _ : ℕ => ℝ) 2 :=
  ∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i

/-- The named synthesis function is exactly the finite sum expression. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_eq_sum
    (k n : ℕ) (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitSynthesis k n c =
      ∑ i : Fin 2, c i • concreteL2MathlibFinTwoUnitFamily k n i := by
  rfl

/-- The synthesis function unfolds to the explicit two-term combination. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_eq_explicit
    (k n : ℕ) (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitSynthesis k n c =
      c 0 • concreteL2MathlibFinTwoUnitFamily k n 0 +
        c 1 • concreteL2MathlibFinTwoUnitFamily k n 1 := by
  unfold concreteL2MathlibFinTwoUnitSynthesis
  exact concrete_l2_mathlib_fin_two_unit_sum_eq_explicit k n c

/-- Kernel-triviality of the named two-unit synthesis function. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_eq_zero_iff
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ} :
    concreteL2MathlibFinTwoUnitSynthesis k n c = 0 ↔
      ∀ i : Fin 2, c i = 0 := by
  unfold concreteL2MathlibFinTwoUnitSynthesis
  exact concrete_l2_mathlib_fin_two_unit_sum_eq_zero_iff hkn

/-- If the named two-unit synthesis vanishes, then the coefficient function is
pointwise zero. -/
theorem concrete_l2_mathlib_fin_two_unit_coefficients_zero_of_synthesis_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hzero : concreteL2MathlibFinTwoUnitSynthesis k n c = 0) :
    ∀ i : Fin 2, c i = 0 := by
  exact (concrete_l2_mathlib_fin_two_unit_synthesis_eq_zero_iff hkn).mp hzero

/-- If all coefficients vanish, then the named two-unit synthesis vanishes. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_zero_of_coefficients_zero
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hcoeff : ∀ i : Fin 2, c i = 0) :
    concreteL2MathlibFinTwoUnitSynthesis k n c = 0 := by
  exact (concrete_l2_mathlib_fin_two_unit_synthesis_eq_zero_iff hkn).mpr hcoeff

/-- The zero coefficient function synthesizes to zero. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_zero_coefficients
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSynthesis k n (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
  unfold concreteL2MathlibFinTwoUnitSynthesis
  simp

/-- Adapter predicate for the named two-unit synthesis kernel layer. -/
def concreteL2MathlibFinTwoUnitSynthesisKernelAdapter : Prop :=
  ∀ {k n : ℕ}, k ≠ n → ∀ {c : Fin 2 → ℝ},
    (concreteL2MathlibFinTwoUnitSynthesis k n c = 0 →
      ∀ i : Fin 2, c i = 0) ∧
    (concreteL2MathlibFinTwoUnitSynthesis k n c = 0 ↔
      ∀ i : Fin 2, c i = 0)

/-- Adapter theorem for the named two-unit synthesis kernel layer. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_kernel_adapter_ready :
    concreteL2MathlibFinTwoUnitSynthesisKernelAdapter := by
  intro k n hkn c
  exact ⟨
    by intro hzero; exact concrete_l2_mathlib_fin_two_unit_coefficients_zero_of_synthesis_zero hkn hzero,
    concrete_l2_mathlib_fin_two_unit_synthesis_eq_zero_iff hkn⟩

/-- Surface for the named two-unit synthesis kernel theorem in Mathlib completed
`ℓ²(ℕ, ℝ)`.

This layer names the finite synthesis operation
`c ↦ ∑ i : Fin 2, c i • e_i` and proves that its zero fiber is exactly the zero
coefficient function.  It is the immediate kernel-trivial handoff toward a later
linear-map API layer, while deliberately preserving the boundary that no general
finite-family `LinearIndependent` theorem or `LinearMap` theorem is claimed here. -/
structure ConcreteL2MathlibFinTwoUnitSynthesisKernelSurface where
  finsetSumReady : concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumSurfaceReady
  synthesisKernelAdapter : concreteL2MathlibFinTwoUnitSynthesisKernelAdapter
  boundaryNotLinearMapTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete named two-unit synthesis kernel surface. -/
def concreteL2MathlibFinTwoUnitSynthesisKernelSurface :
    ConcreteL2MathlibFinTwoUnitSynthesisKernelSurface :=
  { finsetSumReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_finset_sum_surface_ready
    synthesisKernelAdapter :=
      concrete_l2_mathlib_fin_two_unit_synthesis_kernel_adapter_ready
    boundaryNotLinearMapTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the named two-unit synthesis kernel surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitFinsetSumSurfaceReady ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelAdapter ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotLinearMapTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitSynthesisKernelSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the named two-unit synthesis kernel surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_kernel_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_finset_sum_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_synthesis_kernel_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the named two-unit synthesis kernel surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelSurfaceReady

/-- Boundary theorem for the named two-unit synthesis kernel surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_kernel_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisKernelHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_kernel_surface_ready

end

end MathlibAnalytic
end MGAP4D
