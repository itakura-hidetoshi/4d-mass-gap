import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalOperatorGraph

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The `k`-th coordinate unit as a point of the R2 diagonal-operator domain. -/
def concreteL2R2DiagonalOperatorDomainUnit (k : ℕ) :
    ConcreteL2R2DiagonalOperatorDomain :=
  ⟨concreteL2MathlibUnit k, concrete_l2_r2_diagonal_domain_candidate_mathlib_unit k⟩

/-- The expected graph output for the `k`-th coordinate unit: the same coordinate
unit scaled by the diagonal weight at `k`. -/
def concreteL2R2DiagonalOperatorUnitOutput (k : ℕ) :
    ConcreteL2R1HilbertCarrier :=
  concreteL2R2DiagonalWeight k • (concreteL2MathlibUnit k : ConcreteL2R1HilbertCarrier)

/-- Coordinate formula for the diagonal graph on a coordinate unit. -/
theorem concrete_l2_r2_diagonal_operator_unit_graph
    (k : ℕ) :
    concreteL2R2DiagonalOperatorGraph
      (concreteL2R2DiagonalOperatorDomainUnit k)
      (concreteL2R2DiagonalOperatorUnitOutput k) := by
  intro n
  by_cases hnk : n = k
  · subst hnk
    simp [concreteL2R2DiagonalOperatorUnitOutput,
      concreteL2R2DiagonalOperatorDomainUnit,
      concreteL2R2DiagonalOperatorGraph,
      concreteL2R2WeightedCoordinate,
      concrete_l2_mathlib_unit_apply_self]
  · simp [concreteL2R2DiagonalOperatorUnitOutput,
      concreteL2R2DiagonalOperatorDomainUnit,
      concreteL2R2DiagonalOperatorGraph,
      concreteL2R2WeightedCoordinate,
      lp.coeFn_smul,
      concrete_l2_mathlib_unit_apply_ne hnk]

/-- Coordinate-unit graph output is unique at every coordinate. -/
theorem concrete_l2_r2_diagonal_operator_unit_graph_output_coordinate_unique
    (k : ℕ) {y : ConcreteL2R1HilbertCarrier}
    (hy : concreteL2R2DiagonalOperatorGraph
      (concreteL2R2DiagonalOperatorDomainUnit k) y)
    (n : ℕ) :
    y n = concreteL2R2DiagonalOperatorUnitOutput k n := by
  exact concrete_l2_r2_diagonal_operator_graph_coordinate_unique
    (concreteL2R2DiagonalOperatorDomainUnit k) hy
    (concrete_l2_r2_diagonal_operator_unit_graph k) n

/-- The coordinate-unit graph witness is nonzero in the input coordinate: its
input vector has norm one. -/
theorem concrete_l2_r2_diagonal_operator_domain_unit_norm_one
    (k : ℕ) :
    ‖(concreteL2R2DiagonalOperatorDomainUnit k).1‖ = 1 := by
  exact concrete_l2_mathlib_unit_norm_eq_one k

/-- Adapter predicate for coordinate-unit graph witnesses. -/
def concreteL2R2CoordinateUnitGraphWitnessAdapter : Prop :=
  ∀ k : ℕ,
    concreteL2R2DiagonalOperatorGraph
      (concreteL2R2DiagonalOperatorDomainUnit k)
      (concreteL2R2DiagonalOperatorUnitOutput k) ∧
    ‖(concreteL2R2DiagonalOperatorDomainUnit k).1‖ = 1

/-- Adapter theorem for coordinate-unit graph witnesses. -/
theorem concrete_l2_r2_coordinate_unit_graph_witness_adapter_ready :
    concreteL2R2CoordinateUnitGraphWitnessAdapter := by
  intro k
  exact ⟨
    concrete_l2_r2_diagonal_operator_unit_graph k,
    concrete_l2_r2_diagonal_operator_domain_unit_norm_one k⟩

/-- R2g coordinate-unit graph witness surface.

This supplies explicit graph witnesses for every coordinate unit.  It is a graph
witness layer only: not a closed-operator theorem, not unboundedness,
not self-adjointness, not PVM construction, and not a spectral atom theorem. -/
structure ConcreteL2R2CoordinateUnitGraphWitnessSurface where
  diagonalOperatorGraphReady : concreteAnalyticSpineL2R2DiagonalOperatorGraphSurfaceReady
  unitDomainPoint : ℕ → ConcreteL2R2DiagonalOperatorDomain
  unitGraphOutput : ℕ → ConcreteL2R1HilbertCarrier
  unitGraphLaw : ∀ k : ℕ,
    concreteL2R2DiagonalOperatorGraph (unitDomainPoint k) (unitGraphOutput k)
  unitInputNormOne : ∀ k : ℕ, ‖(unitDomainPoint k).1‖ = 1
  boundaryNotOperatorBundled : Prop
  boundaryNotUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2g coordinate-unit graph witness surface. -/
def concreteL2R2CoordinateUnitGraphWitnessSurface :
    ConcreteL2R2CoordinateUnitGraphWitnessSurface :=
  { diagonalOperatorGraphReady :=
      concrete_analytic_spine_l2_r2_diagonal_operator_graph_surface_ready
    unitDomainPoint := concreteL2R2DiagonalOperatorDomainUnit
    unitGraphOutput := concreteL2R2DiagonalOperatorUnitOutput
    unitGraphLaw := concrete_l2_r2_diagonal_operator_unit_graph
    unitInputNormOne := concrete_l2_r2_diagonal_operator_domain_unit_norm_one
    boundaryNotOperatorBundled := True
    boundaryNotUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2g coordinate-unit graph witness readiness. -/
def concreteAnalyticSpineL2R2CoordinateUnitGraphWitnessSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalOperatorGraphSurfaceReady ∧
  concreteL2R2CoordinateUnitGraphWitnessAdapter ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotOperatorBundled ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotUnboundednessTheorem ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotPVMConstruction ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2R2CoordinateUnitGraphWitnessSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2g. -/
theorem concrete_analytic_spine_l2_r2_coordinate_unit_graph_witness_surface_ready :
    concreteAnalyticSpineL2R2CoordinateUnitGraphWitnessSurfaceReady := by
  unfold concreteAnalyticSpineL2R2CoordinateUnitGraphWitnessSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_diagonal_operator_graph_surface_ready <|
      And.intro concrete_l2_r2_coordinate_unit_graph_witness_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the R2g coordinate-unit graph witness surface. -/
def concreteAnalyticSpineL2R2CoordinateUnitGraphWitnessHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2CoordinateUnitGraphWitnessSurfaceReady

/-- Boundary theorem for the R2g coordinate-unit graph witness surface. -/
theorem concrete_analytic_spine_l2_r2_coordinate_unit_graph_witness_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2CoordinateUnitGraphWitnessHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_coordinate_unit_graph_witness_surface_ready

end

end MathlibAnalytic
end MGAP4D
