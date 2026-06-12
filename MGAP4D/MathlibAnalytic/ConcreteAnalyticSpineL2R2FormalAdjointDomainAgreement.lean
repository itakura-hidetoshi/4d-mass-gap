import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointOperatorValue
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalPartialOperatorValue

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The formal-adjoint domain candidate is exactly the domain of the completed
 diagonal graph-defined operator.

This is a genuine adjoint-domain agreement theorem at the graph-defined operator
level.  It follows from the already proved equality between the completed
diagonal graph and the formal-adjoint graph candidate. -/
theorem concrete_l2_r2_formal_adjoint_domain_eq_completed_diagonal_operator_domain :
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate =
      concreteL2R2CompletedDiagonalGraphDefinedOperator.domainCarrier := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨w, hw⟩
    have hwGraph :
        (y, w) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
      rw [concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate]
      exact hw
    exact
      (concreteL2R2CompletedDiagonalGraphDefinedOperator.graphDomainProjectionLaw y).2
        ⟨w, hwGraph⟩
  · intro hy
    rcases
        (concreteL2R2CompletedDiagonalGraphDefinedOperator.graphDomainProjectionLaw y).1 hy with
      ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate]
    exact hw

/-- The same domain agreement read against the original completed diagonal
operator-domain carrier. -/
theorem concrete_l2_r2_formal_adjoint_domain_eq_completed_diagonal_domain_carrier :
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate =
      concreteL2R2CompletedDiagonalOperatorDomainCarrier := by
  exact concrete_l2_r2_formal_adjoint_domain_eq_completed_diagonal_operator_domain

/-- On the common domain, the chosen formal-adjoint value equals the chosen value
of the completed diagonal partial operator.

Thus the graph-level formal adjoint does not merely have the same graph carrier;
it has the same domain and the same operator value pointwise. -/
theorem concrete_l2_r2_formal_adjoint_operator_value_eq_completed_diagonal_operator_value
    (y : lp (fun _ : ℕ => ℝ) 2)
    (hy : y ∈ concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) :
    concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy =
      concreteL2R2CompletedDiagonalOperatorValue
        ⟨y, by
          rw [← concrete_l2_r2_formal_adjoint_domain_eq_completed_diagonal_domain_carrier]
          exact hy⟩ := by
  let yd : ConcreteL2R2CompletedDiagonalOperatorDomain :=
    ⟨y, by
      rw [← concrete_l2_r2_formal_adjoint_domain_eq_completed_diagonal_domain_carrier]
      exact hy⟩
  have hFormal :
      (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate :=
    concrete_l2_r2_formal_adjoint_operator_value_mem y hy
  have hCompleted :
      (y, concreteL2R2CompletedDiagonalFormalAdjointOperatorValue y hy) ∈
        concreteL2R2CompletedDiagonalGraphCarrier := by
    exact concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph hFormal
  have hValue :=
    concrete_l2_r2_completed_diagonal_operator_value_eq_of_graph yd hCompleted
  simpa [yd] using hValue.symm

end

end MathlibAnalytic
end MGAP4D
