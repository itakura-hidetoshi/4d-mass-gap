import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Every coefficient vector classifies a unique vector in the finite synthesis
range via the range-local synthesis equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_exists_unique_range_vector_for_coordinates
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    ∃! v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v = c := by
  refine ⟨concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c, ?_, ?_⟩
  · exact concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c
  · intro v hv
    apply concrete_l2_mathlib_fin_n_synthesis_range_ext_of_coordinates_eq hφ
    rw [hv]
    exact (concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c).symm

/-- The classifier vector for a coefficient function is exactly its synthesized
range vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_unique_classifier_eq_equiv_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    (hv : concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v = c) :
    v = concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c := by
  apply concrete_l2_mathlib_fin_n_synthesis_range_ext_of_coordinates_eq hφ
  rw [hv]
  exact (concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c).symm

/-- Pointwise coordinate classifier form. -/
theorem concrete_l2_mathlib_fin_n_synthesis_exists_unique_range_vector_for_coordinates_pointwise
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    ∃! v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      ∀ i : Fin m,
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i = c i := by
  refine ⟨concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c, ?_, ?_⟩
  · intro i
    exact concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply_apply hφ c i
  · intro v hv
    apply concrete_l2_mathlib_fin_n_synthesis_range_ext hφ
    intro i
    rw [hv i]
    exact (concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply_apply hφ c i).symm

/-- Adapter predicate for the coordinate-classifier layer. -/
def concreteL2MathlibFinNSynthesisCoordinateClassifierAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ),
    ∃! v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v = c

/-- Adapter theorem for the coordinate-classifier layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_classifier_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateClassifierAdapter := by
  intro m φ hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_exists_unique_range_vector_for_coordinates hφ c

/-- Surface for the coordinate-classifier layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateClassifierSurface where
  coordinateExtensionalityReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalitySurfaceReady
  coordinateClassifierAdapter : concreteL2MathlibFinNSynthesisCoordinateClassifierAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete coordinate-classifier surface. -/
def concreteL2MathlibFinNSynthesisCoordinateClassifierSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateClassifierSurface :=
  { coordinateExtensionalityReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_extensionality_surface_ready
    coordinateClassifierAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_classifier_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the coordinate-classifier surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalitySurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the coordinate-classifier surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_extensionality_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_classifier_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the coordinate-classifier surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierSurfaceReady

/-- Hard-residual boundary theorem for the coordinate-classifier surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_surface_ready

end

end MathlibAnalytic
end MGAP4D
