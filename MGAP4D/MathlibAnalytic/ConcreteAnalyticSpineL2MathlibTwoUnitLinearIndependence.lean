import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibUnitPairSeparation

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Two distinct Mathlib completed-`ℓ²(ℕ, ℝ)` coordinate units are linearly
independent in the concrete two-vector sense.

The proof is coordinatewise.  Evaluating
`a • e_k + b • e_n = 0` at coordinate `k` gives `a = 0`; evaluating at
coordinate `n` gives `b = 0`.  This is deliberately a two-vector scalar
coefficient theorem, not yet a general finite-family `LinearIndependent`
theorem. -/
theorem concrete_l2_mathlib_two_unit_linear_independent_coefficients
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ}
    (hlin : a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n = 0) :
    a = 0 ∧ b = 0 := by
  have hkcoord :
      (a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n) k =
        (0 : lp (fun _ : ℕ => ℝ) 2) k := by
    exact congrArg (fun f : lp (fun _ : ℕ => ℝ) 2 => f k) hlin
  have hacoord : a = 0 := by
    simpa [concreteL2MathlibUnit, hkn] using hkcoord
  have hncoord :
      (a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n) n =
        (0 : lp (fun _ : ℕ => ℝ) 2) n := by
    exact congrArg (fun f : lp (fun _ : ℕ => ℝ) 2 => f n) hlin
  have hbcoord : b = 0 := by
    have hnk : n ≠ k := by
      exact hkn.symm
    simpa [concreteL2MathlibUnit, hnk] using hncoord
  exact ⟨hacoord, hbcoord⟩

/-- If a two-term linear combination of distinct coordinate units vanishes, its
first coefficient vanishes. -/
theorem concrete_l2_mathlib_two_unit_linear_independent_left_coeff
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ}
    (hlin : a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n = 0) :
    a = 0 := by
  exact (concrete_l2_mathlib_two_unit_linear_independent_coefficients hkn hlin).1

/-- If a two-term linear combination of distinct coordinate units vanishes, its
second coefficient vanishes. -/
theorem concrete_l2_mathlib_two_unit_linear_independent_right_coeff
    {k n : ℕ} (hkn : k ≠ n) {a b : ℝ}
    (hlin : a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n = 0) :
    b = 0 := by
  exact (concrete_l2_mathlib_two_unit_linear_independent_coefficients hkn hlin).2

/-- Adapter predicate for the concrete two-unit linear-independence layer. -/
def concreteL2MathlibTwoUnitLinearIndependenceAdapter : Prop :=
  ∀ {k n : ℕ}, k ≠ n → ∀ {a b : ℝ},
    a • concreteL2MathlibUnit k + b • concreteL2MathlibUnit n = 0 →
      a = 0 ∧ b = 0

/-- Two-unit linear-independence adapter theorem. -/
theorem concrete_l2_mathlib_two_unit_linear_independence_adapter_ready :
    concreteL2MathlibTwoUnitLinearIndependenceAdapter := by
  intro k n hkn a b hlin
  exact concrete_l2_mathlib_two_unit_linear_independent_coefficients hkn hlin

/-- Surface for two-coordinate-unit linear independence in Mathlib completed
`ℓ²(ℕ, ℝ)`.

This upgrades pairwise metric/additive separation to the first genuine linear
algebra leaf: two distinct coordinate units admit no nontrivial two-term scalar
linear relation.  It remains below the later obligations: no general finite
family theorem, no basis theorem, no dense-span theorem, no finite-support-domain
equivalence, no unbounded-operator domain theorem, no self-adjointness, no PVM,
and no spectral atom claim. -/
structure ConcreteL2MathlibTwoUnitLinearIndependenceSurface where
  pairSeparationReady : concreteAnalyticSpineL2MathlibUnitPairSeparationSurfaceReady
  twoUnitLinearIndependenceAdapter : concreteL2MathlibTwoUnitLinearIndependenceAdapter
  boundaryNotGeneralFiniteFamilyTheorem : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete Mathlib completed-`ℓ²` two-coordinate-unit linear-independence surface. -/
def concreteL2MathlibTwoUnitLinearIndependenceSurface :
    ConcreteL2MathlibTwoUnitLinearIndependenceSurface :=
  { pairSeparationReady :=
      concrete_analytic_spine_l2_mathlib_unit_pair_separation_surface_ready
    twoUnitLinearIndependenceAdapter :=
      concrete_l2_mathlib_two_unit_linear_independence_adapter_ready
    boundaryNotGeneralFiniteFamilyTheorem := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the Mathlib completed-`ℓ²` two-coordinate-unit linear-independence surface. -/
def concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibUnitPairSeparationSurfaceReady ∧
  concreteL2MathlibTwoUnitLinearIndependenceAdapter ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotGeneralFiniteFamilyTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibTwoUnitLinearIndependenceSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the Mathlib completed-`ℓ²` two-coordinate-unit linear-independence surface. -/
theorem concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_surface_ready :
    concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_unit_pair_separation_surface_ready <|
      And.intro concrete_l2_mathlib_two_unit_linear_independence_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the Mathlib completed-`ℓ²` two-coordinate-unit linear-independence surface. -/
def concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceSurfaceReady

/-- Boundary theorem for the Mathlib completed-`ℓ²` two-coordinate-unit linear-independence surface. -/
theorem concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibTwoUnitLinearIndependenceHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_two_unit_linear_independence_surface_ready

end

end MathlibAnalytic
end MGAP4D
