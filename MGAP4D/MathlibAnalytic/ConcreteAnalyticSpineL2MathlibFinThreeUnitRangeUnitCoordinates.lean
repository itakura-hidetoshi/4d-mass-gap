import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinates

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The first selected coordinate unit as an element of the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitFirstRangeVector (a b c : ℕ) :
    concreteL2MathlibFinThreeUnitSynthesisRange a b c :=
  ⟨concreteL2MathlibUnit a, concrete_l2_mathlib_fin_three_unit_first_mem_range a b c⟩

/-- The second selected coordinate unit as an element of the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitSecondRangeVector (a b c : ℕ) :
    concreteL2MathlibFinThreeUnitSynthesisRange a b c :=
  ⟨concreteL2MathlibUnit b, concrete_l2_mathlib_fin_three_unit_second_mem_range a b c⟩

/-- The third selected coordinate unit as an element of the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitThirdRangeVector (a b c : ℕ) :
    concreteL2MathlibFinThreeUnitSynthesisRange a b c :=
  ⟨concreteL2MathlibUnit c, concrete_l2_mathlib_fin_three_unit_third_mem_range a b c⟩

/-- The first selected range unit is synthesized by the first standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_three_unit_first_range_vector_synthesized_by_standard_coeff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0) =
      concreteL2MathlibFinThreeUnitFirstRangeVector a b c := by
  apply Subtype.ext
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply_val]
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply_eq_sum]
  rw [Fin.sum_univ_three]
  simp [concreteL2MathlibFinThreeUnitFamily, concreteL2MathlibFinThreeUnitFirstRangeVector]

/-- The second selected range unit is synthesized by the second standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_three_unit_second_range_vector_synthesized_by_standard_coeff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        (fun i : Fin 3 => if i = 1 then (1 : ℝ) else 0) =
      concreteL2MathlibFinThreeUnitSecondRangeVector a b c := by
  apply Subtype.ext
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply_val]
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply_eq_sum]
  rw [Fin.sum_univ_three]
  simp [concreteL2MathlibFinThreeUnitFamily, concreteL2MathlibFinThreeUnitSecondRangeVector]

/-- The third selected range unit is synthesized by the third standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_three_unit_third_range_vector_synthesized_by_standard_coeff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        (fun i : Fin 3 => if i = 2 then (1 : ℝ) else 0) =
      concreteL2MathlibFinThreeUnitThirdRangeVector a b c := by
  apply Subtype.ext
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_apply_val]
  rw [concrete_l2_mathlib_fin_three_unit_synthesis_linear_map_apply_eq_sum]
  rw [Fin.sum_univ_three]
  simp [concreteL2MathlibFinThreeUnitFamily, concreteL2MathlibFinThreeUnitThirdRangeVector]

/-- The reconstructed coordinates of the first selected range unit are the first
standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_three_unit_first_range_coordinates_eq_standard
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc
        (concreteL2MathlibFinThreeUnitFirstRangeVector a b c) =
      (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0) := by
  exact Eq.symm <|
    concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc
      (concrete_l2_mathlib_fin_three_unit_first_range_vector_synthesized_by_standard_coeff hab hac hbc)

/-- The reconstructed coordinates of the second selected range unit are the second
standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_three_unit_second_range_coordinates_eq_standard
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc
        (concreteL2MathlibFinThreeUnitSecondRangeVector a b c) =
      (fun i : Fin 3 => if i = 1 then (1 : ℝ) else 0) := by
  exact Eq.symm <|
    concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc
      (concrete_l2_mathlib_fin_three_unit_second_range_vector_synthesized_by_standard_coeff hab hac hbc)

/-- The reconstructed coordinates of the third selected range unit are the third
standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_three_unit_third_range_coordinates_eq_standard
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc
        (concreteL2MathlibFinThreeUnitThirdRangeVector a b c) =
      (fun i : Fin 3 => if i = 2 then (1 : ℝ) else 0) := by
  exact Eq.symm <|
    concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc
      (concrete_l2_mathlib_fin_three_unit_third_range_vector_synthesized_by_standard_coeff hab hac hbc)

/-- Adapter predicate for the selected range-unit coordinate layer. -/
def concreteL2MathlibFinThreeUnitRangeUnitCoordinatesAdapter : Prop :=
  ∀ {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c),
    concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc
        (concreteL2MathlibFinThreeUnitFirstRangeVector a b c) =
      (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc
        (concreteL2MathlibFinThreeUnitSecondRangeVector a b c) =
      (fun i : Fin 3 => if i = 1 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc
        (concreteL2MathlibFinThreeUnitThirdRangeVector a b c) =
      (fun i : Fin 3 => if i = 2 then (1 : ℝ) else 0)

/-- Adapter theorem for the selected range-unit coordinate layer. -/
theorem concrete_l2_mathlib_fin_three_unit_range_unit_coordinates_adapter_ready :
    concreteL2MathlibFinThreeUnitRangeUnitCoordinatesAdapter := by
  intro a b c hab hac hbc
  exact ⟨
    concrete_l2_mathlib_fin_three_unit_first_range_coordinates_eq_standard hab hac hbc,
    concrete_l2_mathlib_fin_three_unit_second_range_coordinates_eq_standard hab hac hbc,
    concrete_l2_mathlib_fin_three_unit_third_range_coordinates_eq_standard hab hac hbc⟩

/-- Surface for the coordinate values of the three selected range units.

This layer identifies the reconstructed coordinates of the three selected range
unit vectors with the three standard coefficient functions in `Fin 3 → ℝ`. -/
structure ConcreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface where
  rangeCoordinatesReady : concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesSurfaceReady
  rangeUnitCoordinatesAdapter : concreteL2MathlibFinThreeUnitRangeUnitCoordinatesAdapter
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete selected range-unit coordinate surface. -/
def concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface :
    ConcreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface :=
  { rangeCoordinatesReady := concrete_analytic_spine_l2_mathlib_fin_three_unit_range_coordinates_surface_ready
    rangeUnitCoordinatesAdapter := concrete_l2_mathlib_fin_three_unit_range_unit_coordinates_adapter_ready
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the selected range-unit coordinate surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesSurfaceReady ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesAdapter ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitRangeUnitCoordinatesSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the selected range-unit coordinate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_range_unit_coordinates_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_range_coordinates_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_range_unit_coordinates_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the selected range-unit coordinate surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesSurfaceReady

/-- Boundary theorem for the selected range-unit coordinate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_range_unit_coordinates_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitRangeUnitCoordinatesHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_range_unit_coordinates_surface_ready

end

end MathlibAnalytic
end MGAP4D
