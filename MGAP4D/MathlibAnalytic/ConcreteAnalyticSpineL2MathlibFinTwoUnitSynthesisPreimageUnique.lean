import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRange

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Equality of two synthesized vectors is equivalent to equality of their
coefficient functions.

This is the direct injectivity form of the two-unit synthesis `LinearMap`. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_eq_iff
    {k n : ℕ} (hkn : k ≠ n) {c d : Fin 2 → ℝ} :
    concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
        concreteL2MathlibFinTwoUnitSynthesisLinearMap k n d ↔
      c = d := by
  constructor
  · intro h
    exact concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_injective hkn h
  · intro h
    subst h
    rfl

/-- Pointwise coefficient equality follows from equality of synthesized vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_coefficients_eq_of_map_eq
    {k n : ℕ} (hkn : k ≠ n) {c d : Fin 2 → ℝ}
    (hmap : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
        concreteL2MathlibFinTwoUnitSynthesisLinearMap k n d) :
    ∀ i : Fin 2, c i = d i := by
  have hcd : c = d :=
    (concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_eq_iff hkn).mp hmap
  intro i
  exact congrArg (fun f : Fin 2 → ℝ => f i) hcd

/-- A vector in the two-unit synthesis range has at most one coefficient
preimage under the synthesis linear map. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique
    {k n : ℕ} (hkn : k ≠ n) {v : lp (fun _ : ℕ => ℝ) 2}
    {c d : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = v)
    (hd : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n d = v) :
    c = d := by
  apply concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_injective hkn
  rw [hc, hd]

/-- Pointwise version of preimage uniqueness for a range vector. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique_pointwise
    {k n : ℕ} (hkn : k ≠ n) {v : lp (fun _ : ℕ => ℝ) 2}
    {c d : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = v)
    (hd : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n d = v) :
    ∀ i : Fin 2, c i = d i := by
  have hcd : c = d :=
    concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique hkn hc hd
  intro i
  exact congrArg (fun f : Fin 2 → ℝ => f i) hcd

/-- The first coordinate-unit coefficient witness is unique among all witnesses
for the first selected coordinate unit. -/
theorem concrete_l2_mathlib_fin_two_unit_first_preimage_unique
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
        concreteL2MathlibUnit k) :
    c = (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
  have hwitness :
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n
          (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) =
        concreteL2MathlibUnit k := by
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [Fin.sum_univ_two]
    simp [concreteL2MathlibFinTwoUnitFamily]
  exact concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique hkn hc hwitness

/-- The second coordinate-unit coefficient witness is unique among all witnesses
for the second selected coordinate unit. -/
theorem concrete_l2_mathlib_fin_two_unit_second_preimage_unique
    {k n : ℕ} (hkn : k ≠ n) {c : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
        concreteL2MathlibUnit n) :
    c = (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  have hwitness :
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n
          (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) =
        concreteL2MathlibUnit n := by
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [Fin.sum_univ_two]
    simp [concreteL2MathlibFinTwoUnitFamily]
  exact concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique hkn hc hwitness

/-- Adapter predicate for the two-unit synthesis preimage-uniqueness layer. -/
def concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueAdapter : Prop :=
  ∀ {k n : ℕ}, k ≠ n →
    (∀ {c d : Fin 2 → ℝ},
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
          concreteL2MathlibFinTwoUnitSynthesisLinearMap k n d →
        c = d) ∧
    (∀ {v : lp (fun _ : ℕ => ℝ) 2} {c d : Fin 2 → ℝ},
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c = v →
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n d = v →
        c = d)

/-- Adapter theorem for the two-unit synthesis preimage-uniqueness layer. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique_adapter_ready :
    concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueAdapter := by
  intro k n hkn
  exact ⟨
    by
      intro c d hmap
      exact (concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_eq_iff hkn).mp hmap,
    by
      intro v c d hc hd
      exact concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique hkn hc hd⟩

/-- Surface for preimage uniqueness of the `Fin 2` coordinate-unit synthesis
linear map.

This layer uses the already proved injectivity of the synthesis `LinearMap` to
show that coefficient witnesses for range vectors are unique.  It is the natural
pre-equivalence handoff before any future `LinearEquiv` or range equivalence
construction. -/
structure ConcreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface where
  synthesisRangeReady : concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeSurfaceReady
  preimageUniqueAdapter : concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueAdapter
  boundaryNotRangeEquivTheorem : Prop
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete preimage-uniqueness surface for the two-unit synthesis linear map. -/
def concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface :
    ConcreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface :=
  { synthesisRangeReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_surface_ready
    preimageUniqueAdapter :=
      concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique_adapter_ready
    boundaryNotRangeEquivTheorem := True
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit synthesis preimage-uniqueness surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeSurfaceReady ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueAdapter ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotRangeEquivTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitSynthesisPreimageUniqueSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit synthesis preimage-uniqueness surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_preimage_unique_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_synthesis_preimage_unique_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit synthesis preimage-uniqueness surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueSurfaceReady

/-- Boundary theorem for the two-unit synthesis preimage-uniqueness surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_preimage_unique_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisPreimageUniqueHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_preimage_unique_surface_ready

end

end MathlibAnalytic
end MGAP4D
