import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoff
import MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheorem

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Compact-plaquette input handoff for the dense diagonal `LinearPMap` lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffSurface where
  observableTheoremInputReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffReady
  compactPlaquetteReviewReady :
    compactPlaquetteConstructionTheoremReviewSurface.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  constructedCompactSupport :
    singletonCompactPlaquetteConstructionTheoremData.compactSupport
      (singletonCompactPlaquetteConstructionTheoremData.constructObservable
        singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)
  constructedCentered :
    singletonCompactPlaquetteConstructionTheoremData.centered
      (singletonCompactPlaquetteConstructionTheoremData.constructObservable
        singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)
  constructedSmeared :
    singletonCompactPlaquetteConstructionTheoremData.smeared
      (singletonCompactPlaquetteConstructionTheoremData.constructObservable
        singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)
  chosenObservableDef :
    singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      singletonCompactPlaquetteConstructionTheoremData.constructObservable
        singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette
  boundaryConcreteLatticeGaugePlaquetteStillSeparate : Prop

/-- Concrete compact-plaquette input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffSurface :=
  { observableTheoremInputReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_theorem_input_handoff_ready
    compactPlaquetteReviewReady :=
      compact_plaquette_construction_theorem_review_surface_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    constructedCompactSupport :=
      singleton_compact_plaquette_constructed_compact_support
    constructedCentered :=
      singleton_compact_plaquette_constructed_centered
    constructedSmeared :=
      singleton_compact_plaquette_constructed_smeared
    chosenObservableDef :=
      singleton_compact_plaquette_chosen_observable_def
    boundaryConcreteLatticeGaugePlaquetteStillSeparate := True }

/-- Public readiness predicate for the compact-plaquette input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffReady ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  singletonCompactPlaquetteConstructionTheoremData.compactSupport
    (singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  singletonCompactPlaquetteConstructionTheoremData.centered
    (singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  singletonCompactPlaquetteConstructionTheoremData.smeared
    (singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
    singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette ∧
  concreteL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffSurface.boundaryConcreteLatticeGaugePlaquetteStillSeparate

/-- The compact-plaquette input handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_compact_plaquette_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_theorem_input_handoff_ready,
    compact_plaquette_construction_theorem_review_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    singleton_compact_plaquette_constructed_compact_support,
    singleton_compact_plaquette_constructed_centered,
    singleton_compact_plaquette_constructed_smeared,
    singleton_compact_plaquette_chosen_observable_def,
    trivial⟩

/-- Boundary marker for the compact-plaquette input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffReady

/-- The compact-plaquette input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_compact_plaquette_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_compact_plaquette_input_handoff_ready

end

end MathlibAnalytic
end MGAP4D