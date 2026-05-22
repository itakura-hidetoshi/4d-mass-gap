import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeDecomposition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The first distinguished range vector is nonzero. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_vector_ne_zero
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠ 0 := by
  intro hzero
  have hval := congrArg
    (fun v : concreteL2MathlibFinTwoUnitSynthesisRange k n =>
      (v : lp (fun _ : ℕ => ℝ) 2)) hzero
  have hunit : concreteL2MathlibUnit k = 0 := by
    simpa [concreteL2MathlibFinTwoUnitFirstRangeVector] using hval
  exact concrete_l2_mathlib_unit_ne_zero k hunit

/-- The second distinguished range vector is nonzero. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_vector_ne_zero
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSecondRangeVector k n ≠ 0 := by
  intro hzero
  have hval := congrArg
    (fun v : concreteL2MathlibFinTwoUnitSynthesisRange k n =>
      (v : lp (fun _ : ℕ => ℝ) 2)) hzero
  have hunit : concreteL2MathlibUnit n = 0 := by
    simpa [concreteL2MathlibFinTwoUnitSecondRangeVector] using hval
  exact concrete_l2_mathlib_unit_ne_zero n hunit

/-- The two distinguished range vectors are distinct when the selected indices
are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_ne
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
  intro hEq
  have hval := congrArg
    (fun v : concreteL2MathlibFinTwoUnitSynthesisRange k n =>
      (v : lp (fun _ : ℕ => ℝ) 2)) hEq
  exact concrete_l2_mathlib_unit_ne_of_ne hkn hval

/-- The two-unit synthesis range has a nonzero vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_has_nonzero_vector
    (k n : ℕ) :
    ∃ v : concreteL2MathlibFinTwoUnitSynthesisRange k n, v ≠ 0 :=
  ⟨concreteL2MathlibFinTwoUnitFirstRangeVector k n,
    concrete_l2_mathlib_fin_two_unit_first_range_vector_ne_zero k n⟩

/-- The two-unit synthesis range has two distinct vectors when the selected
indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_has_two_distinct_vectors
    {k n : ℕ} (hkn : k ≠ n) :
    ∃ v w : concreteL2MathlibFinTwoUnitSynthesisRange k n, v ≠ w :=
  ⟨concreteL2MathlibFinTwoUnitFirstRangeVector k n,
    concreteL2MathlibFinTwoUnitSecondRangeVector k n,
    concrete_l2_mathlib_fin_two_unit_range_vectors_ne hkn⟩

/-- The two-unit synthesis range is not subsingleton when the selected indices
are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_not_subsingleton
    {k n : ℕ} (hkn : k ≠ n) :
    ¬ Subsingleton (concreteL2MathlibFinTwoUnitSynthesisRange k n) := by
  intro hsub
  rcases concrete_l2_mathlib_fin_two_unit_range_has_two_distinct_vectors hkn with
    ⟨v, w, hvw⟩
  exact hvw (Subsingleton.elim v w)

/-- The two-unit synthesis range is not the bottom submodule when the first
selected coordinate unit is used as a witness. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_range_ne_bot
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n ≠
      (⊥ : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2)) := by
  intro hbot
  have hmem : (concreteL2MathlibUnit k : lp (fun _ : ℕ => ℝ) 2) ∈
      (⊥ : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2)) := by
    rw [← hbot]
    exact concrete_l2_mathlib_fin_two_unit_first_mem_range k n
  have hzero : concreteL2MathlibUnit k = 0 := by
    simpa using hmem
  exact concrete_l2_mathlib_unit_ne_zero k hzero

/-- Adapter predicate for the nontriviality of the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeNontrivialAdapter : Prop :=
  (∀ k n : ℕ,
    ∃ v : concreteL2MathlibFinTwoUnitSynthesisRange k n, v ≠ 0) ∧
  (∀ k n : ℕ,
    concreteL2MathlibFinTwoUnitSynthesisRange k n ≠
      (⊥ : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2))) ∧
  (∀ {k n : ℕ}, k ≠ n →
    ∃ v w : concreteL2MathlibFinTwoUnitSynthesisRange k n, v ≠ w)

/-- Adapter theorem for the nontriviality of the two-unit synthesis range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_nontrivial_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeNontrivialAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_has_nonzero_vector k n,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_synthesis_range_ne_bot k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_has_two_distinct_vectors hkn⟩

/-- Surface for nontriviality of the two-unit synthesis range.

This layer records that the range is not bottom and contains nonzero and, for
`k ≠ n`, distinct distinguished range vectors.  It remains a two-coordinate range
surface and does not claim finite dimensionality of the ambient space, a basis
theorem, dense span, finite-support-domain equivalence, or any operator-theoretic
conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeNontrivialSurface where
  rangeDecompositionReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionSurfaceReady
  rangeNontrivialAdapter : concreteL2MathlibFinTwoUnitRangeNontrivialAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete nontriviality surface for the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeNontrivialSurface :
    ConcreteL2MathlibFinTwoUnitRangeNontrivialSurface :=
  { rangeDecompositionReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_decomposition_surface_ready
    rangeNontrivialAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_nontrivial_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range nontriviality surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDecompositionSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialAdapter ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeNontrivialSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range nontriviality surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_decomposition_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_nontrivial_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range nontriviality surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialSurfaceReady

/-- Boundary theorem for the two-unit range nontriviality surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_surface_ready

end

end MathlibAnalytic
end MGAP4D
