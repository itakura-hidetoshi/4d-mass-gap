import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainSubmodule

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Every point of the promoted dense diagonal-domain submodule has the original
bare diagonal-domain-candidate proof. -/
theorem concrete_l2_r2_diagonal_domain_candidate_submodule_mem_candidate
    (x : concreteL2R2DiagonalDomainCandidateSubmodule) :
    ConcreteL2R2DiagonalDomainCandidate (x : ConcreteL2R1HilbertCarrier) := by
  have hx :
      (x : ConcreteL2R1HilbertCarrier) ∈
        (concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier) := x.2
  rw [concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq] at hx
  exact hx

/-- The promoted dense submodule can be viewed transparently as the
domain-candidate carrier used by the diagonal action formula. -/
abbrev concreteL2R2DenseDiagonalDomainCarrier : Type :=
  concreteL2R2DiagonalDomainCandidateSubmodule

/-- Forget a dense-domain carrier point to the R1 Hilbert carrier. -/
def concreteL2R2DenseDiagonalDomainCarrierVal
    (x : concreteL2R2DenseDiagonalDomainCarrier) : ConcreteL2R1HilbertCarrier :=
  (x : ConcreteL2R1HilbertCarrier)

/-- Domain-candidate proof carried by every dense-domain carrier point. -/
theorem concrete_l2_r2_dense_diagonal_domain_carrier_mem_candidate
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    ConcreteL2R2DiagonalDomainCandidate (concreteL2R2DenseDiagonalDomainCarrierVal x) := by
  unfold concreteL2R2DenseDiagonalDomainCarrierVal
  exact concrete_l2_r2_diagonal_domain_candidate_submodule_mem_candidate x

/-- Raw diagonal action on the promoted dense-domain carrier, still as a raw
coordinate formula.  The next layer will package this as an `lp`-valued action
and then as a linear map. -/
def concreteL2R2DenseDiagonalDomainRawAction
    (x : concreteL2R2DenseDiagonalDomainCarrier) : ℕ → ℝ :=
  concreteL2R2DiagonalRawAction (concreteL2R2DenseDiagonalDomainCarrierVal x)

/-- The raw dense-domain action is definitionally the R2 weighted coordinate
formula. -/
theorem concrete_l2_r2_dense_diagonal_domain_raw_action_eq_weighted
    (x : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainRawAction x n =
      concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n := by
  rfl

/-- Dense-domain carrier bridge surface. -/
structure ConcreteL2R2DenseDiagonalDomainCarrierBridgeSurface where
  denseSubmoduleReady : concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleSurfaceReady
  carrier : Type
  carrierVal : carrier → ConcreteL2R1HilbertCarrier
  carrierMemCandidate : ∀ x : carrier, ConcreteL2R2DiagonalDomainCandidate (carrierVal x)
  rawAction : carrier → ℕ → ℝ
  rawActionEqWeighted :
    ∀ x : carrier, ∀ n : ℕ,
      rawAction x n = concreteL2R2WeightedCoordinate (carrierVal x) n
  boundaryNotLpValuedAction : Prop
  boundaryNotLinearMap : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain carrier bridge surface. -/
def concreteL2R2DenseDiagonalDomainCarrierBridgeSurface :
    ConcreteL2R2DenseDiagonalDomainCarrierBridgeSurface :=
  { denseSubmoduleReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_submodule_surface_ready
    carrier := concreteL2R2DenseDiagonalDomainCarrier
    carrierVal := concreteL2R2DenseDiagonalDomainCarrierVal
    carrierMemCandidate := concrete_l2_r2_dense_diagonal_domain_carrier_mem_candidate
    rawAction := concreteL2R2DenseDiagonalDomainRawAction
    rawActionEqWeighted := concrete_l2_r2_dense_diagonal_domain_raw_action_eq_weighted
    boundaryNotLpValuedAction := True
    boundaryNotLinearMap := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the dense-domain carrier bridge. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleSurfaceReady ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    ConcreteL2R2DiagonalDomainCandidate (concreteL2R2DenseDiagonalDomainCarrierVal x)) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainRawAction x n =
      concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n) ∧
  concreteL2R2DenseDiagonalDomainCarrierBridgeSurface.boundaryNotLpValuedAction ∧
  concreteL2R2DenseDiagonalDomainCarrierBridgeSurface.boundaryNotLinearMap ∧
  concreteL2R2DenseDiagonalDomainCarrierBridgeSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainCarrierBridgeSurface.boundaryNotSelfAdjointness

/-- The dense-domain carrier bridge surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_carrier_bridge_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_submodule_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_carrier_mem_candidate,
    concrete_l2_r2_dense_diagonal_domain_raw_action_eq_weighted,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the dense-domain carrier now carries the raw action formula,
but the action has not yet been promoted to an `lp`-valued linear map. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeSurfaceReady

/-- Boundary theorem for the dense-domain carrier bridge. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_carrier_bridge_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_carrier_bridge_surface_ready

end

end MathlibAnalytic
end MGAP4D
