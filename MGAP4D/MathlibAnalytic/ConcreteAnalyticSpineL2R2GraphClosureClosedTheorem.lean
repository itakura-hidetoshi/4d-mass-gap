import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphClosednessObligationPromotion
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityTargetRefinement

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Closedness of the graph-norm closure carrier. -/
def concreteL2R2GraphClosureClosedTheorem : Prop :=
  @IsClosed ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- The graph-norm closure carrier is closed by `isClosed_closure`. -/
theorem concrete_l2_r2_graph_norm_closure_carrier_closed :
    concreteL2R2GraphClosureClosedTheorem := by
  unfold concreteL2R2GraphClosureClosedTheorem
  unfold concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget
  exact @isClosed_closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2FiniteSupportCoreGraphCarrier

/-- Boundary: the closure carrier is closed, but this file does not identify the
concrete diagonal graph with that closure. -/
def concreteL2R2GraphClosureBoundaryNotDiagonalGraphEqualsClosure : Prop :=
  concreteL2R2GraphClosednessObligationPromotionReady ∧
  concreteL2R2GraphClosureClosedTheorem

/-- The diagonal-graph-equals-closure boundary is proof-bearing. -/
theorem concrete_l2_r2_graph_closure_boundary_not_diagonal_graph_equals_closure :
    concreteL2R2GraphClosureBoundaryNotDiagonalGraphEqualsClosure := by
  exact ⟨
    concrete_analytic_spine_l2_r2_graph_closedness_obligation_promotion_ready,
    concrete_l2_r2_graph_norm_closure_carrier_closed⟩

/-- Boundary: this file proves closedness of the closure carrier, but does not
promote the graph-closedness theorem. -/
def concreteL2R2GraphClosureBoundaryNotGraphClosednessTheorem : Prop :=
  concreteL2R2GraphClosureBoundaryNotDiagonalGraphEqualsClosure ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotGraphClosednessTheorem

/-- The graph-closedness theorem boundary is proof-bearing at the closure-closed
layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_graph_closedness_theorem :
    concreteL2R2GraphClosureBoundaryNotGraphClosednessTheorem := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_diagonal_graph_equals_closure,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_graph_closedness_theorem⟩

/-- Boundary: this file does not promote closure uniqueness. -/
def concreteL2R2GraphClosureBoundaryNotClosureUniquenessTheorem : Prop :=
  concreteL2R2GraphClosureBoundaryNotGraphClosednessTheorem ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotClosureUniquenessTheorem

/-- The closure-uniqueness boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_closure_uniqueness_theorem :
    concreteL2R2GraphClosureBoundaryNotClosureUniquenessTheorem := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_graph_closedness_theorem,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_closure_uniqueness_theorem⟩

/-- Boundary: this file does not promote a closed-operator theorem. -/
def concreteL2R2GraphClosureBoundaryNotClosedOperatorTheorem : Prop :=
  concreteL2R2GraphClosureBoundaryNotClosureUniquenessTheorem ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotClosedOperatorTheorem

/-- The closed-operator boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_closed_operator_theorem :
    concreteL2R2GraphClosureBoundaryNotClosedOperatorTheorem := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_closure_uniqueness_theorem,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_closed_operator_theorem⟩

/-- Boundary: this file does not assert essential self-adjointness. -/
def concreteL2R2GraphClosureBoundaryNotEssentialSelfAdjointness : Prop :=
  concreteL2R2GraphClosureBoundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotEssentialSelfAdjointness

/-- The essential-self-adjointness boundary is proof-bearing at the closure-closed
layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_essential_self_adjointness :
    concreteL2R2GraphClosureBoundaryNotEssentialSelfAdjointness := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_closed_operator_theorem,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_essential_self_adjointness⟩

/-- Boundary: this file does not assert self-adjointness. -/
def concreteL2R2GraphClosureBoundaryNotSelfAdjointnessTheorem : Prop :=
  concreteL2R2GraphClosureBoundaryNotEssentialSelfAdjointness ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotSelfAdjointnessTheorem

/-- The self-adjointness boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_self_adjointness_theorem :
    concreteL2R2GraphClosureBoundaryNotSelfAdjointnessTheorem := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_essential_self_adjointness,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_self_adjointness_theorem⟩

/-- Boundary: this file does not apply the spectral theorem. -/
def concreteL2R2GraphClosureBoundaryNotSpectralTheoremApplication : Prop :=
  concreteL2R2GraphClosureBoundaryNotSelfAdjointnessTheorem ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotSpectralTheoremApplication

/-- The spectral-theorem boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_spectral_theorem_application :
    concreteL2R2GraphClosureBoundaryNotSpectralTheoremApplication := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_self_adjointness_theorem,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_spectral_theorem_application⟩

/-- Boundary: this file does not construct a PVM. -/
def concreteL2R2GraphClosureBoundaryNotPVMConstruction : Prop :=
  concreteL2R2GraphClosureBoundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotPVMConstruction

/-- The PVM boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_pvm_construction :
    concreteL2R2GraphClosureBoundaryNotPVMConstruction := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_spectral_theorem_application,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_pvm_construction⟩

/-- Boundary: this file does not assert the exact atom `33/20`. -/
def concreteL2R2GraphClosureBoundaryNotExactAtomThirtyThreeTwentieth : Prop :=
  concreteL2R2GraphClosureBoundaryNotPVMConstruction ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotExactAtomThirtyThreeTwentieth

/-- The exact-atom boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_exact_atom_thirty_three_twentieth :
    concreteL2R2GraphClosureBoundaryNotExactAtomThirtyThreeTwentieth := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_pvm_construction,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_exact_atom_thirty_three_twentieth⟩

/-- Boundary: this file does not assert positive spectral weight. -/
def concreteL2R2GraphClosureBoundaryNotPositiveSpectralWeight : Prop :=
  concreteL2R2GraphClosureBoundaryNotExactAtomThirtyThreeTwentieth ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotPositiveSpectralWeight

/-- The positive-spectral-weight boundary is proof-bearing at the closure-closed
layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_positive_spectral_weight :
    concreteL2R2GraphClosureBoundaryNotPositiveSpectralWeight := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_exact_atom_thirty_three_twentieth,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_positive_spectral_weight⟩

/-- Boundary: this file does not identify the physical Yang--Mills Hamiltonian. -/
def concreteL2R2GraphClosureBoundaryNotPhysicalYangMillsHamiltonian : Prop :=
  concreteL2R2GraphClosureBoundaryNotPositiveSpectralWeight ∧
  concreteL2R2GraphClosednessObligationPromotionBoundaryNotPhysicalYangMillsHamiltonian

/-- The physical-Hamiltonian boundary is proof-bearing at the closure-closed layer. -/
theorem concrete_l2_r2_graph_closure_boundary_not_physical_yang_mills_hamiltonian :
    concreteL2R2GraphClosureBoundaryNotPhysicalYangMillsHamiltonian := by
  exact ⟨
    concrete_l2_r2_graph_closure_boundary_not_positive_spectral_weight,
    concrete_l2_r2_graph_closedness_obligation_promotion_boundary_not_physical_yang_mills_hamiltonian⟩

structure ConcreteL2R2GraphClosureClosedTheoremSurface where
  graphClosednessObligationPromotionReady :
    concreteL2R2GraphClosednessObligationPromotionReady
  closureCarrierClosed : concreteL2R2GraphClosureClosedTheorem
  boundaryNotDiagonalGraphEqualsClosure :
    concreteL2R2GraphClosureBoundaryNotDiagonalGraphEqualsClosure
  boundaryNotGraphClosednessTheorem :
    concreteL2R2GraphClosureBoundaryNotGraphClosednessTheorem
  boundaryNotClosureUniquenessTheorem :
    concreteL2R2GraphClosureBoundaryNotClosureUniquenessTheorem
  boundaryNotClosedOperatorTheorem :
    concreteL2R2GraphClosureBoundaryNotClosedOperatorTheorem
  boundaryNotEssentialSelfAdjointness :
    concreteL2R2GraphClosureBoundaryNotEssentialSelfAdjointness
  boundaryNotSelfAdjointnessTheorem :
    concreteL2R2GraphClosureBoundaryNotSelfAdjointnessTheorem
  boundaryNotSpectralTheoremApplication :
    concreteL2R2GraphClosureBoundaryNotSpectralTheoremApplication
  boundaryNotPVMConstruction : concreteL2R2GraphClosureBoundaryNotPVMConstruction
  boundaryNotExactAtomThirtyThreeTwentieth :
    concreteL2R2GraphClosureBoundaryNotExactAtomThirtyThreeTwentieth
  boundaryNotPositiveSpectralWeight :
    concreteL2R2GraphClosureBoundaryNotPositiveSpectralWeight
  boundaryNotPhysicalYangMillsHamiltonian :
    concreteL2R2GraphClosureBoundaryNotPhysicalYangMillsHamiltonian

def concreteL2R2GraphClosureClosedTheoremSurface :
    ConcreteL2R2GraphClosureClosedTheoremSurface :=
  { graphClosednessObligationPromotionReady :=
      concrete_analytic_spine_l2_r2_graph_closedness_obligation_promotion_ready
    closureCarrierClosed := concrete_l2_r2_graph_norm_closure_carrier_closed
    boundaryNotDiagonalGraphEqualsClosure :=
      concrete_l2_r2_graph_closure_boundary_not_diagonal_graph_equals_closure
    boundaryNotGraphClosednessTheorem :=
      concrete_l2_r2_graph_closure_boundary_not_graph_closedness_theorem
    boundaryNotClosureUniquenessTheorem :=
      concrete_l2_r2_graph_closure_boundary_not_closure_uniqueness_theorem
    boundaryNotClosedOperatorTheorem :=
      concrete_l2_r2_graph_closure_boundary_not_closed_operator_theorem
    boundaryNotEssentialSelfAdjointness :=
      concrete_l2_r2_graph_closure_boundary_not_essential_self_adjointness
    boundaryNotSelfAdjointnessTheorem :=
      concrete_l2_r2_graph_closure_boundary_not_self_adjointness_theorem
    boundaryNotSpectralTheoremApplication :=
      concrete_l2_r2_graph_closure_boundary_not_spectral_theorem_application
    boundaryNotPVMConstruction :=
      concrete_l2_r2_graph_closure_boundary_not_pvm_construction
    boundaryNotExactAtomThirtyThreeTwentieth :=
      concrete_l2_r2_graph_closure_boundary_not_exact_atom_thirty_three_twentieth
    boundaryNotPositiveSpectralWeight :=
      concrete_l2_r2_graph_closure_boundary_not_positive_spectral_weight
    boundaryNotPhysicalYangMillsHamiltonian :=
      concrete_l2_r2_graph_closure_boundary_not_physical_yang_mills_hamiltonian }

/-- Readiness predicate for the R2 graph-closure closed theorem surface. -/
def concreteL2R2GraphClosureClosedTheoremReady : Prop :=
  concreteL2R2GraphClosednessObligationPromotionReady ∧
  concreteL2R2GraphClosureClosedTheorem ∧
  concreteL2R2GraphClosureBoundaryNotDiagonalGraphEqualsClosure ∧
  concreteL2R2GraphClosureBoundaryNotGraphClosednessTheorem ∧
  concreteL2R2GraphClosureBoundaryNotClosureUniquenessTheorem ∧
  concreteL2R2GraphClosureBoundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphClosureBoundaryNotEssentialSelfAdjointness ∧
  concreteL2R2GraphClosureBoundaryNotSelfAdjointnessTheorem ∧
  concreteL2R2GraphClosureBoundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphClosureBoundaryNotPVMConstruction ∧
  concreteL2R2GraphClosureBoundaryNotExactAtomThirtyThreeTwentieth ∧
  concreteL2R2GraphClosureBoundaryNotPositiveSpectralWeight ∧
  concreteL2R2GraphClosureBoundaryNotPhysicalYangMillsHamiltonian

/-- The R2 graph-norm closure carrier closed theorem is ready. -/
theorem concrete_analytic_spine_l2_r2_graph_closure_closed_theorem_ready :
    concreteL2R2GraphClosureClosedTheoremReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_graph_closedness_obligation_promotion_ready,
    concrete_l2_r2_graph_norm_closure_carrier_closed,
    concrete_l2_r2_graph_closure_boundary_not_diagonal_graph_equals_closure,
    concrete_l2_r2_graph_closure_boundary_not_graph_closedness_theorem,
    concrete_l2_r2_graph_closure_boundary_not_closure_uniqueness_theorem,
    concrete_l2_r2_graph_closure_boundary_not_closed_operator_theorem,
    concrete_l2_r2_graph_closure_boundary_not_essential_self_adjointness,
    concrete_l2_r2_graph_closure_boundary_not_self_adjointness_theorem,
    concrete_l2_r2_graph_closure_boundary_not_spectral_theorem_application,
    concrete_l2_r2_graph_closure_boundary_not_pvm_construction,
    concrete_l2_r2_graph_closure_boundary_not_exact_atom_thirty_three_twentieth,
    concrete_l2_r2_graph_closure_boundary_not_positive_spectral_weight,
    concrete_l2_r2_graph_closure_boundary_not_physical_yang_mills_hamiltonian⟩

end

end MathlibAnalytic
end MGAP4D
