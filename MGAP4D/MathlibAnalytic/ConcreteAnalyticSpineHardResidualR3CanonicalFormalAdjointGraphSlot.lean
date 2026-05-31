import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3MathlibAdjointGraphInstantiationSlot

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Canonical formal slot for the R3 adjoint graph adapter.

This fills the abstract slot with the already constructed concrete formal
adjoint linear-map graph.  It is not the final Mathlib adjoint graph
instantiation; it is the closed formal reference slot against which the future
Mathlib graph will be identified. -/
def concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot :
    ConcreteAnalyticSpineHardResidualR3MathlibAdjointGraphSlot where
  mathlibAdjointGraph := concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph
  identifiesFormalAdjointGraph := by
    rfl

/-- The canonical formal slot identifies its graph with the formal adjoint graph by reflexivity. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_identifies_formal_graph :
    concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification
      concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph := by
  exact concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.identifiesFormalAdjointGraph

/-- The canonical formal slot graph is definitionally the formal adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_graph_eq_linear_map_graph :
    concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  rfl

/-- The canonical formal slot yields the abstract adapter input. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_adapter_input_ready :
    concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphAdapterInput
      concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph := by
  exact concrete_analytic_spine_hard_residual_r3_slot_adapter_input
    concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot

/-- The canonical formal slot yields the conditional pre-promotion surface. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_conditional_prepromotion_ready :
    concreteAnalyticSpineHardResidualR3ConditionalSelfAdjointPrePromotion
      concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph := by
  exact concrete_analytic_spine_hard_residual_r3_slot_conditional_prepromotion
    concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot

/-- The canonical formal slot yields the slot-level promotion package. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_promotion_package_ready :
    concreteAnalyticSpineHardResidualR3SlotLevelSelfAdjointPromotionPackage
      concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot := by
  exact concrete_analytic_spine_hard_residual_r3_slot_level_self_adjoint_promotion_package_ready
    concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot

/-- Closed canonical formal slot package.

This is the fully proved formal reference instance of the R3 slot machinery.  It
keeps the non-promotion boundary visible while proving that the slot adapter
itself is not the remaining obstruction. -/
def concreteAnalyticSpineHardResidualR3CanonicalFormalSlotClosedPackage : Prop :=
  concreteAnalyticSpineHardResidualR3SlotLevelSelfAdjointPromotionPackage
    concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot ∧
  (concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The canonical formal slot package is closed. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_closed_package_ready :
    concreteAnalyticSpineHardResidualR3CanonicalFormalSlotClosedPackage := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_promotion_package_ready,
    concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_graph_eq_linear_map_graph,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- After closing the canonical formal slot, the remaining R3 task is no longer
slot construction but the external identification of the actual Mathlib adjoint
graph with this canonical formal graph. -/
def concreteAnalyticSpineHardResidualR3AfterCanonicalFormalSlotBlocker : Prop :=
  concreteAnalyticSpineHardResidualR3CanonicalFormalSlotClosedPackage ∧
  concreteAnalyticSpineHardResidualR3PostSlotBlocker ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The post-canonical-formal-slot R3 blocker is visible. -/
theorem concrete_analytic_spine_hard_residual_r3_after_canonical_formal_slot_blocker_visible :
    concreteAnalyticSpineHardResidualR3AfterCanonicalFormalSlotBlocker := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_closed_package_ready,
    concrete_analytic_spine_hard_residual_r3_post_slot_blocker_visible,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

end

end MathlibAnalytic
end MGAP4D
