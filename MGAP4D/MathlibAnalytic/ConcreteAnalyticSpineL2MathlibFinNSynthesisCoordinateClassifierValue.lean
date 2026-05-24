import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- If a range vector is classified by coordinate function `c`, then its
underlying `ℓ²` value is the corresponding finite coordinate-unit synthesis sum. -/
theorem concrete_l2_mathlib_fin_n_synthesis_classifier_val_eq_sum
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    {c : Fin m → ℝ}
    (hv : concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v = c) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) := by
  rw [concrete_l2_mathlib_fin_n_synthesis_range_decompose_val hφ v]
  rw [hv]

/-- Pointwise classifier hypothesis version of the finite synthesis value theorem. -/
theorem concrete_l2_mathlib_fin_n_synthesis_classifier_val_eq_sum_pointwise
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    {c : Fin m → ℝ}
    (hv : ∀ i : Fin m,
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i = c i) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) := by
  apply concrete_l2_mathlib_fin_n_synthesis_classifier_val_eq_sum hφ
  funext i
  exact hv i

/-- The canonical classifier vector for `c` has the finite synthesis value
`∑ i, c i • e_(φ i)`. -/
theorem concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_sum
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
      lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_equiv_apply_val_of_injective hφ c

/-- The uniquely classified range vector is value-equal to the canonical finite
synthesis sum. -/
theorem concrete_l2_mathlib_fin_n_synthesis_unique_classifier_val_eq_sum
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    (hv : concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v = c) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
        lp (fun _ : ℕ => ℝ) 2) := by
  have hveq := concrete_l2_mathlib_fin_n_synthesis_unique_classifier_eq_equiv_apply hφ c hv
  exact congrArg (fun w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ) =>
      (w : lp (fun _ : ℕ => ℝ) 2)) hveq

/-- Adapter predicate for the coordinate-classifier value layer. -/
def concreteL2MathlibFinNSynthesisCoordinateClassifierValueAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} {c : Fin m → ℝ},
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v = c →
        (v : lp (fun _ : ℕ => ℝ) 2) =
          ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i)

/-- Adapter theorem for the coordinate-classifier value layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateClassifierValueAdapter := by
  intro m φ hφ v c hv
  exact concrete_l2_mathlib_fin_n_synthesis_classifier_val_eq_sum hφ hv

/-- Surface for the coordinate-classifier value layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface where
  coordinateClassifierReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierSurfaceReady
  coordinateClassifierValueAdapter : concreteL2MathlibFinNSynthesisCoordinateClassifierValueAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete coordinate-classifier value surface. -/
def concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface :=
  { coordinateClassifierReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_surface_ready
    coordinateClassifierValueAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the coordinate-classifier value surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateClassifierValueSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the coordinate-classifier value surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the coordinate-classifier value surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueSurfaceReady

/-- Hard-residual boundary theorem for the coordinate-classifier value surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateClassifierValueHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_classifier_value_surface_ready

end

end MathlibAnalytic
end MGAP4D
