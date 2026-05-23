import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitFinsetSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The finite synthesis map associated to three selected coordinate units.

This is the named-function layer before promoting the construction to a
`LinearMap`. -/
def concreteL2MathlibFinThreeUnitSynthesis (a b c : ℕ) (r : Fin 3 → ℝ) :
    lp (fun _ : ℕ => ℝ) 2 :=
  ∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i

/-- The named `Fin 3` synthesis function is exactly the finite-sum expression. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_eq_sum
    (a b c : ℕ) (r : Fin 3 → ℝ) :
    concreteL2MathlibFinThreeUnitSynthesis a b c r =
      ∑ i : Fin 3, r i • concreteL2MathlibFinThreeUnitFamily a b c i := by
  rfl

/-- The named `Fin 3` synthesis function unfolds to the explicit three-term
combination. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_eq_explicit
    (a b c : ℕ) (r : Fin 3 → ℝ) :
    concreteL2MathlibFinThreeUnitSynthesis a b c r =
      r 0 • concreteL2MathlibFinThreeUnitFamily a b c 0 +
        r 1 • concreteL2MathlibFinThreeUnitFamily a b c 1 +
          r 2 • concreteL2MathlibFinThreeUnitFamily a b c 2 := by
  unfold concreteL2MathlibFinThreeUnitSynthesis
  exact concrete_l2_mathlib_fin_three_unit_sum_eq_explicit a b c r

/-- Kernel-triviality of the named three-unit synthesis function. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_eq_zero_iff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ} :
    concreteL2MathlibFinThreeUnitSynthesis a b c r = 0 ↔
      ∀ i : Fin 3, r i = 0 := by
  unfold concreteL2MathlibFinThreeUnitSynthesis
  exact concrete_l2_mathlib_fin_three_unit_sum_eq_zero_iff hab hac hbc

/-- If the named three-unit synthesis vanishes, then the coefficient function is
pointwise zero. -/
theorem concrete_l2_mathlib_fin_three_unit_coefficients_zero_of_synthesis_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hzero : concreteL2MathlibFinThreeUnitSynthesis a b c r = 0) :
    ∀ i : Fin 3, r i = 0 := by
  exact (concrete_l2_mathlib_fin_three_unit_synthesis_eq_zero_iff hab hac hbc).mp hzero

/-- If all coefficients vanish, then the named three-unit synthesis vanishes. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_zero_of_coefficients_zero
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r : Fin 3 → ℝ}
    (hcoeff : ∀ i : Fin 3, r i = 0) :
    concreteL2MathlibFinThreeUnitSynthesis a b c r = 0 := by
  exact (concrete_l2_mathlib_fin_three_unit_synthesis_eq_zero_iff hab hac hbc).mpr hcoeff

/-- The zero coefficient function synthesizes to zero. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_zero_coefficients
    (a b c : ℕ) :
    concreteL2MathlibFinThreeUnitSynthesis a b c (fun _ : Fin 3 => (0 : ℝ)) = 0 := by
  unfold concreteL2MathlibFinThreeUnitSynthesis
  simp

/-- Adapter predicate for the named three-unit synthesis kernel layer. -/
def concreteL2MathlibFinThreeUnitSynthesisKernelAdapter : Prop :=
  ∀ {a b c : ℕ}, a ≠ b → a ≠ c → b ≠ c → ∀ {r : Fin 3 → ℝ},
    (concreteL2MathlibFinThreeUnitSynthesis a b c r = 0 →
      ∀ i : Fin 3, r i = 0) ∧
    (concreteL2MathlibFinThreeUnitSynthesis a b c r = 0 ↔
      ∀ i : Fin 3, r i = 0)

/-- Adapter theorem for the named three-unit synthesis kernel layer. -/
theorem concrete_l2_mathlib_fin_three_unit_synthesis_kernel_adapter_ready :
    concreteL2MathlibFinThreeUnitSynthesisKernelAdapter := by
  intro a b c hab hac hbc r
  exact ⟨
    by intro hzero; exact concrete_l2_mathlib_fin_three_unit_coefficients_zero_of_synthesis_zero hab hac hbc hzero,
    concrete_l2_mathlib_fin_three_unit_synthesis_eq_zero_iff hab hac hbc⟩

/-- Surface for the named three-unit synthesis kernel theorem in Mathlib
completed `ℓ²(ℕ, ℝ)`.

This layer names the finite synthesis operation and proves that its zero fiber is
exactly the zero coefficient function.  It remains below the `LinearMap`, range,
and general finite-family layers. -/
structure ConcreteL2MathlibFinThreeUnitSynthesisKernelSurface where
  finsetSumReady : concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumSurfaceReady
  synthesisKernelAdapter : concreteL2MathlibFinThreeUnitSynthesisKernelAdapter
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

/-- Concrete named three-unit synthesis kernel surface. -/
def concreteL2MathlibFinThreeUnitSynthesisKernelSurface :
    ConcreteL2MathlibFinThreeUnitSynthesisKernelSurface :=
  { finsetSumReady := concrete_analytic_spine_l2_mathlib_fin_three_unit_finset_sum_surface_ready
    synthesisKernelAdapter := concrete_l2_mathlib_fin_three_unit_synthesis_kernel_adapter_ready
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

/-- Readiness for the named three-unit synthesis kernel surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitFinsetSumSurfaceReady ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelAdapter ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotLinearMapTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotRangeEquivTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitSynthesisKernelSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the named three-unit synthesis kernel surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_kernel_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_finset_sum_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_synthesis_kernel_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the named three-unit synthesis kernel surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelSurfaceReady

/-- Boundary theorem for the named three-unit synthesis kernel surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_kernel_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisKernelHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_kernel_surface_ready

end

end MathlibAnalytic
end MGAP4D
