import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentity

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Range vectors are equal if their recovered coordinate functions are equal. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_ext_of_coordinates_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    (hcoord : concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v =
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ w) :
    v = w := by
  exact (concrete_l2_mathlib_fin_n_synthesis_coordinates_bijective hφ).1 hcoord

/-- Coordinate extensionality in pointwise form. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_ext
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    (hcoord : ∀ i : Fin m,
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i =
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ w i) :
    v = w := by
  apply concrete_l2_mathlib_fin_n_synthesis_range_ext_of_coordinates_eq hφ
  funext i
  exact hcoord i

/-- Equivalence between range equality and recovered-coordinate equality. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_eq_iff_coordinates_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} :
    v = w ↔
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v =
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ w := by
  constructor
  · intro hvw
    rw [hvw]
  · intro hcoord
    exact concrete_l2_mathlib_fin_n_synthesis_range_ext_of_coordinates_eq hφ hcoord

/-- Pointwise equivalence between range equality and coordinate equality. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_eq_iff_coordinates_eq_pointwise
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} :
    v = w ↔
      ∀ i : Fin m,
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i =
          concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ w i := by
  constructor
  · intro hvw i
    rw [hvw]
  · intro hcoord
    exact concrete_l2_mathlib_fin_n_synthesis_range_ext hφ hcoord

/-- Adapter predicate for the coordinate-extensionality layer. -/
def concreteL2MathlibFinNSynthesisCoordinateExtensionalityAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ {v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)},
      (v = w ↔
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v =
          concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ w)

/-- Adapter theorem for the coordinate-extensionality layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_extensionality_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateExtensionalityAdapter := by
  intro m φ hφ v w
  exact concrete_l2_mathlib_fin_n_synthesis_range_eq_iff_coordinates_eq hφ

/-- Surface for the coordinate-extensionality layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface where
  projectionIdentityReady : concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentitySurfaceReady
  coordinateExtensionalityAdapter : concreteL2MathlibFinNSynthesisCoordinateExtensionalityAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete coordinate-extensionality surface. -/
def concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface :
    ConcreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface :=
  { projectionIdentityReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_projection_identity_surface_ready
    coordinateExtensionalityAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_extensionality_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the coordinate-extensionality surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentitySurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalityAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateExtensionalitySurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the coordinate-extensionality surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_extensionality_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalitySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_projection_identity_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_extensionality_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the coordinate-extensionality surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalitySurfaceReady

/-- Hard-residual boundary theorem for the coordinate-extensionality surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_extensionality_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateExtensionalityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_extensionality_surface_ready

end

end MathlibAnalytic
end MGAP4D
