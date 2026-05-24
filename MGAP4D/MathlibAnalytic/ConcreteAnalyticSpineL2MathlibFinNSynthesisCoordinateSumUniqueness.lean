import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValue

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- If a range vector has finite synthesis value with coefficient function `c`,
then `c` is exactly its recovered coordinate function. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_coordinates_of_val_eq_sum
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} {c : Fin m → ℝ}
    (hv : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i)) :
    c = concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_decompose_coefficients_unique hφ hv

/-- Two finite coordinate-unit synthesis sums that classify the same range vector
have equal coefficient functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_coefficients_unique_for_range_vector
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} {c d : Fin m → ℝ}
    (hc : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i))
    (hd : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i)) :
    c = d := by
  have hc' := concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_coordinates_of_val_eq_sum hφ hc
  have hd' := concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_coordinates_of_val_eq_sum hφ hd
  exact hc'.trans hd'.symm

/-- Pointwise form of uniqueness of finite coordinate-unit synthesis coefficients
for a fixed range vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_coefficients_unique_for_range_vector_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} {c d : Fin m → ℝ}
    (hc : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i))
    (hd : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i))
    (i : Fin m) :
    c i = d i := by
  exact congrFun
    (concrete_l2_mathlib_fin_n_synthesis_sum_coefficients_unique_for_range_vector hφ hc hd) i

/-- The canonical finite synthesis sum has unique coefficient function. -/
theorem concrete_l2_mathlib_fin_n_synthesis_equiv_apply_coefficients_unique
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) {c d : Fin m → ℝ}
    (hd : (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
      lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i)) :
    d = c := by
  have hc : (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
      lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) :=
    concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_sum hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_sum_coefficients_unique_for_range_vector hφ hd hc

/-- Adapter predicate for the coordinate-sum uniqueness layer. -/
def concreteL2MathlibFinNSynthesisCoordinateSumUniquenessAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} {c d : Fin m → ℝ},
      (v : lp (fun _ : ℕ => ℝ) 2) =
        ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) →
      (v : lp (fun _ : ℕ => ℝ) 2) =
        ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i) →
      c = d

/-- Adapter theorem for the coordinate-sum uniqueness layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateSumUniquenessAdapter := by
  intro m φ hφ v c d hc hd
  exact concrete_l2_mathlib_fin_n_synthesis_sum_coefficients_unique_for_range_vector hφ hc hd

/-- Surface for the coordinate-sum uniqueness layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface where
  coordinateClassifierValueReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueSurfaceReady
  coordinateSumUniquenessAdapter : concreteL2MathlibFinNSynthesisCoordinateSumUniquenessAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete coordinate-sum uniqueness surface. -/
def concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface :=
  { coordinateClassifierValueReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_surface_ready
    coordinateSumUniquenessAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the coordinate-sum uniqueness surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSumUniquenessSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the coordinate-sum uniqueness surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the coordinate-sum uniqueness surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessSurfaceReady

/-- Hard-residual boundary theorem for the coordinate-sum uniqueness surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_surface_ready

end

end MathlibAnalytic
end MGAP4D
